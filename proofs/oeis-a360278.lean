import OMAStatements.S_oeis_a360278

open OMA.S_oeis_a360278

namespace A360278Proof

theorem D_cast {K : Type*} [CommRing K] (f : ℕ → ℤ) (n : ℕ) :
    ((D f n : ℤ) : K) = (Matrix.of fun j k : Fin n =>
      (f ((j : ℕ) + 1 + ((k : ℕ) + 1)) : K) + if j = k then 1 else 0).det := by
  rw [D, show ∀ x : ℤ, (x : K) = Int.castRingHom K x from fun _ => rfl, RingHom.map_det]
  congr 1
  ext j k
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, map_add]
  split_ifs <;> simp

theorem sum_fin {K : Type*} [CommRing K] (n : ℕ) (c x y : K) :
    ∑ j : Fin n, c * x ^ ((j : ℕ) + 1) * y ^ ((j : ℕ) + 1) =
      c * ∑ j ∈ Finset.range n, (x * y) ^ (j + 1) := by
  rw [Fin.sum_univ_eq_sum_range (fun j => c * x ^ (j + 1) * y ^ (j + 1)) n, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

-- det (1 + U V) for the rank two matrix [c a^(j+k) + d b^(j+k)].
theorem det_rank2 {K : Type*} [CommRing K] (n : ℕ) (a b c d : K) (g : ℕ → K)
    (hg : ∀ m, g m = c * a ^ m + d * b ^ m) :
    (Matrix.of fun j k : Fin n => g ((j : ℕ) + 1 + ((k : ℕ) + 1)) + if j = k then 1 else 0).det =
      (1 + c * ∑ j ∈ Finset.range n, (a * a) ^ (j + 1)) *
        (1 + d * ∑ j ∈ Finset.range n, (b * b) ^ (j + 1)) -
        c * d * (∑ j ∈ Finset.range n, (a * b) ^ (j + 1)) ^ 2 := by
  let U : Matrix (Fin n) (Fin 2) K := Matrix.of fun j i => ![a, b] i ^ ((j : ℕ) + 1)
  let V : Matrix (Fin 2) (Fin n) K := Matrix.of fun i k => ![c, d] i * ![a, b] i ^ ((k : ℕ) + 1)
  have hM : (Matrix.of fun j k : Fin n => g ((j : ℕ) + 1 + ((k : ℕ) + 1)) +
      if j = k then 1 else 0) = 1 + U * V := by
    ext j k
    simp only [Matrix.of_apply, Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply,
      Fin.sum_univ_two, U, V, hg, Matrix.cons_val_zero, Matrix.cons_val_one]
    split_ifs <;> ring
  rw [hM, Matrix.det_one_add_mul_comm, Matrix.det_fin_two]
  simp only [Matrix.add_apply, Matrix.one_apply, Matrix.mul_apply, U, V, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, sum_fin, if_pos]
  simp only [show (0 : Fin 2) ≠ 1 by decide, show (1 : Fin 2) ≠ 0 by decide, if_false,
    zero_add]
  rw [mul_comm b a]
  ring

theorem altsum (m : ℕ) {K : Type*} [CommRing K] :
    ∑ j ∈ Finset.range (2 * m), (-1 : K) ^ (j + 1) = 0 := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show 2 * (m + 1) = 2 * m + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ, ih]
    simp [pow_succ, pow_mul]

theorem hG (x : ℝ) (m : ℕ) :
    (x ^ 2 - 1) * (1 + ∑ j ∈ Finset.range m, (x * x) ^ (j + 1)) = x ^ (2 * (m + 1)) - 1 := by
  induction m with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ]; linear_combination ih

theorem part1 (A : ℤ) (n : ℕ) :
    A ^ 2 * D (vP A) n = vP A (n + 1) ^ 2 - (A ^ 2 + 4) * ((n % 2 : ℕ) : ℤ) := by
  obtain ⟨α, β, hA, hp⟩ : ∃ α β : ℝ, (A : ℝ) = α + β ∧ α * β = -1 := by
    have hr2 : Real.sqrt ((A : ℝ) ^ 2 + 4) ^ 2 = (A : ℝ) ^ 2 + 4 := Real.sq_sqrt (by positivity)
    exact ⟨((A : ℝ) + Real.sqrt ((A : ℝ) ^ 2 + 4)) / 2, ((A : ℝ) - Real.sqrt ((A : ℝ) ^ 2 + 4)) / 2,
      by ring, by linear_combination (-1 / 4 : ℝ) * hr2⟩
  have hv : ∀ m, (vP A m : ℝ) = 1 * α ^ m + 1 * β ^ m := by
    have h2 : ∀ m, (vP A m : ℝ) = α ^ m + β ^ m ∧
        (vP A (m + 1) : ℝ) = α ^ (m + 1) + β ^ (m + 1) := by
      intro m
      induction m with
      | zero =>
        refine ⟨by simp [vP]; norm_num, ?_⟩
        simp [vP, hA]
      | succ m ih =>
        refine ⟨ih.2, ?_⟩
        simp only [vP]
        push_cast
        rw [ih.1, ih.2, hA]
        linear_combination (α ^ m + β ^ m) * hp
    intro m
    rw [(h2 m).1]
    ring
  have hd := det_rank2 n α β 1 1 (fun m => (vP A m : ℝ)) hv
  beta_reduce at hd
  have hs1 : (α ^ 2 - 1) * (β ^ 2 - 1) = -(A : ℝ) ^ 2 := by
    rw [hA]; linear_combination (α * β + 1) * hp
  have hXY : α ^ (2 * (n + 1)) * β ^ (2 * (n + 1)) = 1 := by
    rw [← mul_pow, hp, pow_mul]; norm_num
  have h1 := hG α n
  have h2 := hG β n
  apply Int.cast_injective (α := ℝ)
  rw [Int.cast_mul, Int.cast_pow, D_cast, hd, hp]
  push_cast
  rw [hv (n + 1)]
  simp only [one_mul]
  obtain ⟨P, hP⟩ : ∃ P, P = 1 + ∑ j ∈ Finset.range n, (α * α) ^ (j + 1) := ⟨_, rfl⟩
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = 1 + ∑ j ∈ Finset.range n, (β * β) ^ (j + 1) := ⟨_, rfl⟩
  rw [← hP, ← hQ]
  rw [← hP] at h1
  rw [← hQ] at h2
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hc : (α * β) ^ (2 * m + 1) = -1 := by rw [hp, pow_succ, pow_mul]; norm_num
    rw [altsum, show ((2 * m : ℕ) : ℤ) % 2 = 0 by omega]
    push_cast
    linear_combination P * Q * hs1 - (β ^ 2 - 1) * Q * h1 - (α ^ (2 * (2 * m + 1)) - 1) * h2 -
      hXY - 2 * hc
  · have hc : (α * β) ^ (2 * m + 1 + 1) = 1 := by
      rw [hp, show 2 * m + 1 + 1 = 2 * (m + 1) by ring, pow_mul]; norm_num
    have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [Finset.sum_range_succ, altsum, hodd, show ((2 * m + 1 : ℕ) : ℤ) % 2 = 1 by omega]
    push_cast
    linear_combination P * Q * hs1 - (β ^ 2 - 1) * Q * h1 - (α ^ (2 * (2 * m + 1 + 1)) - 1) * h2 -
      hXY - 2 * hc

theorem uM_mul (A : ℤ) (x y : ℂ) (hA : (A : ℂ) = x + y) (hp : x * y = 1) (m : ℕ) :
    (uM A (m + 1) : ℂ) * x ^ m = ∑ i ∈ Finset.range (m + 1), (x * x) ^ i ∧
      (uM A (m + 2) : ℂ) * x ^ (m + 1) = ∑ i ∈ Finset.range (m + 2), (x * x) ^ i := by
  induction m with
  | zero =>
    refine ⟨by simp [uM], ?_⟩
    simp only [uM, Finset.sum_range_succ, Finset.sum_range_zero]
    push_cast
    rw [hA]
    linear_combination hp
  | succ m ih =>
    obtain ⟨h1, h2⟩ := ih
    refine ⟨h2, ?_⟩
    rw [show m + 1 + 2 = m + 1 + 1 + 1 by ring, uM]
    rw [Finset.sum_range_succ] at h2
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    push_cast
    rw [hA]
    linear_combination (x + y) * x * h2 - x ^ 2 * h1 +
      (∑ i ∈ Finset.range (m + 1), (x * x) ^ i + (x * x) ^ (m + 1)) * hp

theorem hP1 (x : ℂ) (n : ℕ) :
    1 + 1 * ∑ j ∈ Finset.range n, (x * x) ^ (j + 1) = ∑ i ∈ Finset.range (n + 1), (x * x) ^ i := by
  rw [Finset.sum_range_succ', pow_zero, one_mul, add_comm]

theorem part3 (A : ℤ) (n : ℕ) : D (vM A) n = uM A (n + 1) ^ 2 - (n : ℤ) ^ 2 := by
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_pow_nat_eq ((A : ℂ) ^ 2 - 4) two_pos
  obtain ⟨α, β, hA, hp⟩ : ∃ α β : ℂ, (A : ℂ) = α + β ∧ α * β = 1 :=
    ⟨((A : ℂ) + s) / 2, ((A : ℂ) - s) / 2, by ring, by linear_combination (-1 / 4 : ℂ) * hs⟩
  have hv : ∀ m, (vM A m : ℂ) = 1 * α ^ m + 1 * β ^ m := by
    have h2 : ∀ m, (vM A m : ℂ) = α ^ m + β ^ m ∧
        (vM A (m + 1) : ℂ) = α ^ (m + 1) + β ^ (m + 1) := by
      intro m
      induction m with
      | zero =>
        refine ⟨by simp [vM]; norm_num, ?_⟩
        simp [vM, hA]
      | succ m ih =>
        refine ⟨ih.2, ?_⟩
        simp only [vM]
        push_cast
        rw [ih.1, ih.2, hA]
        linear_combination (α ^ m + β ^ m) * hp
    intro m
    rw [(h2 m).1]
    ring
  have hd := det_rank2 n α β 1 1 (fun m => (vM A m : ℂ)) hv
  beta_reduce at hd
  apply Int.cast_injective (α := ℂ)
  rw [D_cast, hd, hp, hP1, hP1, ← (uM_mul A α β hA hp n).1,
    ← (uM_mul A β α (by rw [hA]; ring) (by rw [mul_comm]; exact hp) n).1]
  simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul]
  push_cast
  have hpow : α ^ n * β ^ n = 1 := by rw [← mul_pow, hp, one_pow]
  linear_combination (uM A (n + 1) : ℂ) ^ 2 * hpow

-- Part 4 algebra, with c = 1 / sqrt 5 and sqrt 5 = phi - psi.
theorem alg4 (φ ψ c X Y Φ Ψ T e σ : ℝ) (hc : c * (φ - ψ) = 1) (hs2 : (φ - ψ) ^ 2 = 5)
    (hφψ : φ * ψ = -1) (hXY : X * Y = -1) (hX : X * φ = Φ ^ 2) (hY : ψ * Y = Ψ ^ 2)
    (hΦΨ : Φ * Ψ = σ) (hσ : 2 + T ^ 2 = -2 * σ + 5 * e) :
    (1 + c * (X - φ)) * (1 + -c * (Y - ψ)) - c * -c * T ^ 2 =
      (c * Φ + -c * Ψ) ^ 2 + e := by
  linear_combination c ^ 2 * (hX - hXY - hφψ + hY + hσ + 2 * hΦΨ) -
    (c * (X - ψ) + 1 - c * (Y - ψ)) * hc + e * (1 + c * (φ - ψ)) * hc - e * c ^ 2 * hs2

theorem geo (x : ℝ) (h : x ^ 2 = x + 1) (n : ℕ) :
    ∑ j ∈ Finset.range n, (x * x) ^ (j + 1) = x ^ (2 * n + 1) - x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    linear_combination (-x ^ (2 * n + 1)) * h

theorem part4 (n : ℕ) :
    D (fun m => (Nat.fib m : ℤ)) n = (Nat.fib (n + 1) : ℤ) ^ 2 + ((n % 2 : ℕ) : ℤ) := by
  set c : ℝ := (Real.sqrt 5)⁻¹ with hcdef
  have hg : ∀ m, (((Nat.fib m : ℤ)) : ℝ) = c * Real.goldenRatio ^ m +
      -c * Real.goldenConj ^ m := by
    intro m
    rw [Int.cast_natCast, Real.coe_fib_eq, div_eq_mul_inv]
    ring
  have hd := det_rank2 n Real.goldenRatio Real.goldenConj c (-c)
    (fun m => (((Nat.fib m : ℤ)) : ℝ)) hg
  beta_reduce at hd
  have hc : c * (Real.goldenRatio - Real.goldenConj) = 1 := by
    rw [Real.goldenRatio_sub_goldenConj]; exact inv_mul_cancel₀ (by positivity)
  have hs2 : (Real.goldenRatio - Real.goldenConj) ^ 2 = 5 := by
    rw [Real.goldenRatio_sub_goldenConj]; exact Real.sq_sqrt (by norm_num)
  have hφψ := Real.goldenRatio_mul_goldenConj
  have hXY : Real.goldenRatio ^ (2 * n + 1) * Real.goldenConj ^ (2 * n + 1) = -1 := by
    rw [← mul_pow, hφψ]; exact Odd.neg_one_pow ⟨n, rfl⟩
  have hX : Real.goldenRatio ^ (2 * n + 1) * Real.goldenRatio = (Real.goldenRatio ^ (n + 1)) ^ 2 := by
    ring
  have hY : Real.goldenConj * Real.goldenConj ^ (2 * n + 1) = (Real.goldenConj ^ (n + 1)) ^ 2 := by
    ring
  apply Int.cast_injective (α := ℝ)
  rw [D_cast, hd, Int.cast_add, Int.cast_pow, hg (n + 1), geo _ Real.goldenRatio_sq n,
    geo _ Real.goldenConj_sq n, hφψ]
  obtain ⟨m, rfl | rfl⟩ := Nat.even_or_odd' n
  · have hΦΨ : Real.goldenRatio ^ (2 * m + 1) * Real.goldenConj ^ (2 * m + 1) = -1 := by
      rw [← mul_pow, hφψ]; exact Odd.neg_one_pow ⟨m, rfl⟩
    rw [altsum, show 2 * m % 2 = 0 by omega]
    push_cast
    linear_combination alg4 _ _ c _ _ _ _ 0 0 (-1) hc hs2 hφψ hXY hX hY hΦΨ (by norm_num)
  · have hΦΨ : Real.goldenRatio ^ (2 * m + 1 + 1) * Real.goldenConj ^ (2 * m + 1 + 1) = 1 := by
      rw [← mul_pow, hφψ]; exact Even.neg_one_pow ⟨m + 1, by ring⟩
    have hodd : (-1 : ℝ) ^ (2 * m + 1) = -1 := by rw [pow_succ, pow_mul]; norm_num
    rw [Finset.sum_range_succ, altsum, hodd, show (2 * m + 1) % 2 = 1 by omega]
    push_cast
    linear_combination alg4 _ _ c _ _ _ _ (-1) 1 1 hc hs2 hφψ hXY hX hY hΦΨ (by norm_num)

end A360278Proof

open A360278Proof in
theorem OMA.solution : type_of% @OMA.S_oeis_a360278.main := by
  refine ⟨fun A n _ => part1 A n, fun n _ => ?_, fun A n _ => part3 A n, fun n _ => part4 n⟩
  have h := part1 1 n
  norm_num at h
  exact h

