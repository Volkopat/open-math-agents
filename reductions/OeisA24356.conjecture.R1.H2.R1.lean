import OMAReductions.R_OeisA24356_conjecture_R1
import Mathlib

/-!
# Nonzero prime Hankel determinants and the next prime window

A first failed recurrence produces a larger nonsingular leading minor by
integer column operations. This is the finite step in Kronecker’s Hankel
criterion (see Bakan and Berg, arXiv:1605.01196). The prime sequence has no
nontrivial integer recurrence, so its leading determinants are nonzero at
unbounded orders. The uniqueness reduction separates affine independence
from the extension of an inhomogeneous relation by one prime window.
-/

open Matrix Finset

namespace OMA.R_OeisA24356_conjecture_R1_H2_R1

/-- Affine independence of the columns of each prime Hankel block of order
at least five. Subtracting the first column leaves a rectangular matrix
whose entries are sums of consecutive prime gaps. -/
def H1 : Prop := ∀ (d : ℕ), 4 ≤ d → ∀ b : Fin d → ℤ,
  (∀ i ≤ d, ∑ j, b j * ((Nat.nth Nat.Prime (i + j.val + 1) : ℤ) - Nat.nth Nat.Prime i) = 0) →
  b = 0

/-- The inhomogeneous extension test. If a nonzero multiple of the initial
prime in each window is the same weighted sum of prime increments for
the first d + 1 windows, this identity holds in the next window too. -/
def H2 : Prop := ∀ (d : ℕ), 4 ≤ d → ∀ (b : Fin d → ℤ) (s : ℤ), s ≠ 0 →
  (∀ i ≤ d, ∑ j, b j * ((Nat.nth Nat.Prime (i + j.val + 1) : ℤ) - Nat.nth Nat.Prime i) =
    s * Nat.nth Nat.Prime i) →
  ∑ j, b j * ((Nat.nth Nat.Prime (d + 1 + j.val + 1) : ℤ) - Nat.nth Nat.Prime (d + 1)) =
    s * Nat.nth Nat.Prime (d + 1)



/-- In a finite space, a trajectory whose predecessor is determined by its
successor must return to its initial state. -/
lemma returns {S : Type*} [Finite S] (s : ℕ → S)
    (back : ∀ i j, s (i + 1) = s (j + 1) → s i = s j) :
    ∃ t, 0 < t ∧ s 0 = s t := by
  obtain ⟨i, j, ne, eq⟩ := Finite.exists_ne_map_eq_of_infinite s
  have descend (a b : ℕ) (lt : a < b) (e : s a = s b) : ∃ t, 0 < t ∧ s 0 = s t := by
    induction a generalizing b with
    | zero => exact ⟨b, lt, e⟩
    | succ a ih =>
      obtain ⟨b, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : b ≠ 0)
      exact ih b (by omega) (back a b e)
  rcases lt_or_gt_of_ne ne with h | h
  · exact descend i j h eq
  · exact descend j i h eq.symm

/-- A nonzero coefficient of the earliest prime in a recurrence determines
each window from the next one modulo a suitably large prime. -/
lemma no_first_coeff (d start : ℕ) (c : Fin (d + 1) → ℤ) (hc : c 0 ≠ 0)
    (rel : ∀ i, ∑ j, c j * (Nat.nth Nat.Prime (start + i + j.val) : ℤ) = 0) : False := by
  classical
  let m := start + (c 0).natAbs + 1
  let p := Nat.nth Nat.Prime m
  have mono := Nat.nth_strictMono Nat.infinite_setOfPred_prime
  have large : (c 0).natAbs < p := by
    have lower : m ≤ p := mono.id_le m
    exact lt_of_lt_of_le (by dsimp [m]; omega) lower
  have prime : p.Prime := Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime m
  let _ : Fact p.Prime := ⟨prime⟩
  have nz : (c 0 : ZMod p) ≠ 0 := by
    intro h
    have hd := (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp h
    have habs := Int.natAbs_dvd_natAbs.mpr hd
    simp only [Int.natAbs_natCast] at habs
    exact large.not_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hc) habs)
  let z (i : ℕ) : ZMod p := Nat.nth Nat.Prime (m + i)
  have modrel (i : ℕ) : ∑ j, (c j : ZMod p) * z (i + j.val) = 0 := by
    have eq := congrArg (Int.castRingHom (ZMod p)) (rel (m - start + i))
    simpa [z, show start + (m - start + i) = m + i by dsimp [m]; omega, Nat.add_assoc] using eq
  let s (i : ℕ) (j : Fin (d + 1)) := z (i + j.val)
  have back (i j : ℕ) (e : s (i + 1) = s (j + 1)) : s i = s j := by
    have tail (t : Fin d) : z (i + t.succ.val) = z (j + t.succ.val) := by
      simpa [s, Nat.add_assoc, Nat.add_comm 1] using congrFun e t.castSucc
    have zero : z i = z j := by
      have a := modrel i
      have b := modrel j
      rw [Fin.sum_univ_succ] at a b
      simp only [Fin.val_zero, Nat.add_zero] at a b
      simp_rw [tail] at a
      exact mul_left_cancel₀ nz (add_right_cancel (a.trans b.symm))
    funext t
    exact Fin.cases (by simpa [s] using zero) (fun t => tail t) t
  obtain ⟨t, pos, e⟩ := returns s back
  have div : p ∣ Nat.nth Nat.Prime (m + t) := by
    apply (ZMod.natCast_eq_zero_iff _ _).mp
    have h := congrFun e 0
    simpa [s, z, ← show Nat.nth Nat.Prime m = p from rfl] using h.symm
  have same := (Nat.prime_dvd_prime_iff_eq prime
    (Nat.nth_mem_of_infinite Nat.infinite_setOfPred_prime (m + t))).mp div
  exact (mono (show m < m + t by omega)).ne same

/-- The primes satisfy no nonzero integer linear recurrence, even on a tail. -/
theorem no_recurrence (d start : ℕ) (c : Fin (d + 1) → ℤ)
    (rel : ∀ i, ∑ j, c j * (Nat.nth Nat.Prime (start + i + j.val) : ℤ) = 0) : c = 0 := by
  induction d generalizing start with
  | zero =>
    funext t
    have e : t = 0 := Fin.ext (by omega)
    subst t
    exact by_contra (fun h => no_first_coeff 0 start c h rel)
  | succ d ih =>
    have first : c 0 = 0 := by_contra (fun h => no_first_coeff (d + 1) start c h rel)
    have rest := ih (start + 1) (fun j => c j.succ) (by
      intro i
      have e := rel i
      rw [Fin.sum_univ_succ] at e
      simpa [first, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using e)
    funext t
    exact Fin.cases first (fun j => congrFun rest j) t
/-- Leading prime Hankel determinants are nonzero at unbounded orders. -/
lemma arbitrarily_large : ∀ bound : ℕ, ∃ n ≥ bound, OeisA24356.a n ≠ 0 := by
  classical
  let hankel (f : ℕ → ℤ) (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
    Matrix.of fun i j => f (i.val + j.val)
  let residual {d : ℕ} (f : ℕ → ℤ) (c : Fin (d + 1) → ℤ) (i : ℕ) : ℤ :=
    ∑ k, c k * f (i + k.val)
  /- The adjugate fits an integer recurrence to the first d rows. -/
  have fit (f : ℕ → ℤ) (d : ℕ) :
      ∃ c : Fin (d + 1) → ℤ, c (Fin.last d) = (hankel f d).det ∧
        ∀ i < d, residual f c i = 0 := by
    let A := hankel f d
    let b (i : Fin d) := f (i.val + d)
    let v := A.adjugate *ᵥ b
    let c : Fin (d + 1) → ℤ := Fin.lastCases A.det (fun i => -v i)
    refine ⟨c, by simp [c, A], ?_⟩
    intro i hi
    have h := congrFun (show A *ᵥ v = A.det • b by
      rw [show v = A.adjugate *ᵥ b from rfl, Matrix.mulVec_mulVec, Matrix.mul_adjugate,
        Matrix.smul_mulVec, Matrix.one_mulVec]) (⟨i, hi⟩ : Fin d)
    change (∑ j : Fin d, f (i + j.val) * v j) = A.det * f (i + d) at h
    simp only [residual, Fin.sum_univ_castSucc, c, Fin.lastCases_last, Fin.lastCases_castSucc,
      Fin.val_last, Fin.val_castSucc, neg_mul, Finset.sum_neg_distrib]
    rw [← h]
    simp [mul_comm]

  /- If the first failed window starts at d + r−1, order d + r is a
  nonsingular leading Hankel minor. Reverse the transformed final columns
  to expose a triangular block with the discrepancy on its diagonal. -/
  have recover (f : ℕ → ℤ) (d r : ℕ) (c : Fin (d + 1) → ℤ)
      (initial : (hankel f d).det ≠ 0)
      (good : ∀ t < d + r - 1, residual f c t = 0)
      (failure : residual f c (d + r - 1) ≠ 0) : (hankel f (d + r)).det ≠ 0 := by
    classical
    let e : Fin d ⊕ Fin r ≃ Fin (d + r) := finSumFinEquiv
    let A := (hankel f (d + r)).submatrix e e
    let shift (j : Fin r) (k : Fin (d + 1)) : Fin (d + r) := ⟨j.rev.val + k.val, by
      have := j.rev.isLt; have := k.isLt; omega⟩
    let col : Fin d ⊕ Fin r → (Fin d ⊕ Fin r → ℤ) :=
      Sum.elim (fun j => Pi.single (.inl j) 1)
        (fun j => ∑ k, c k • Pi.single (e.symm (shift j k)) (1 : ℤ))
    let T : Matrix (Fin d ⊕ Fin r) (Fin d ⊕ Fin r) ℤ := Matrix.of fun i j => col j i
    have left (i) (j : Fin d) : (A * T) i (.inl j) = A i (.inl j) := by
      change (A *ᵥ Pi.single (.inl j) 1) i = _
      rw [Matrix.mulVec_single_one]; rfl
    have right (i) (j : Fin r) : (A * T) i (.inr j) = residual f c ((e i).val + j.rev.val) := by
      change (A *ᵥ ∑ k, c k • Pi.single (e.symm (shift j k)) (1 : ℤ)) i = _
      rw [Matrix.mulVec_sum]
      rw [Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro k _
      rw [Matrix.mulVec_smul A (c k), Matrix.mulVec_single_one]
      change c k * f ((e i).val + (e (e.symm (shift j k))).val) = _
      simp [shift, Nat.add_assoc]
    let D : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => residual f c (d + i.val + j.rev.val)
    let C : Matrix (Fin r) (Fin d) ℤ := Matrix.of fun i j => f (d + i.val + j.val)
    have eq : A * T = Matrix.fromBlocks (hankel f d) 0 C D := by
      ext i j
      cases i with
      | inl i =>
        cases j with
        | inl j => simpa [A, e, hankel] using left (.inl i) j
        | inr j =>
          rw [right]
          apply good
          change i.val + j.rev.val < d + r - 1
          have := i.isLt; have := j.rev.isLt; omega
      | inr i =>
        cases j with
        | inl j => simpa [A, C, e, hankel] using left (.inr i) j
        | inr j => exact right (.inr i) j
    have triangular : D.IsLowerTriangular := by
      intro i j h
      apply good
      change d + i.val + (r - (j.val + 1)) < d + r - 1
      change i.val < j.val at h
      have := j.isLt; omega
    have nonzero : D.det ≠ 0 := by
      rw [Matrix.det_of_isLowerTriangular D triangular]
      apply Finset.prod_ne_zero_iff.mpr
      intro i _
      change residual f c (d + i.val + (r - (i.val + 1))) ≠ 0
      rwa [show d + i.val + (r - (i.val + 1)) = d + r - 1 by have := i.isLt; omega]
    intro zero
    have zz : (A * T).det = 0 := by
      rw [Matrix.det_mul, show A.det = _ from Matrix.det_submatrix_equiv_self e _, zero, zero_mul]
    rw [eq, Matrix.det_fromBlocks_zero₁₂] at zz
    exact (mul_ne_zero initial nonzero) zz
  let prime (t : ℕ) : ℤ := Nat.nth Nat.Prime t
  have later (d : ℕ) (hd : OeisA24356.a d ≠ 0) : ∃ n > d, OeisA24356.a n ≠ 0 := by
    obtain ⟨c, last, first⟩ := fit prime d
    have bad : ∃ i : ℕ, residual prime c i ≠ 0 := by
      by_contra! all
      have zero := no_recurrence d 0 c (by simpa [prime, residual] using all)
      exact hd (last.symm.trans (congrFun zero (Fin.last d)))
    let i := Nat.find bad
    have fail : residual prime c i ≠ 0 := Nat.find_spec bad
    have before (j : ℕ) (lt : j < i) : residual prime c j = 0 :=
      not_not.mp (Nat.find_min bad lt)
    have le : d ≤ i := by
      by_contra! h
      exact fail (first i h)
    let r := i + 1 - d
    have total : d + r = i + 1 := by dsimp [r]; omega
    refine ⟨d + r, by omega, recover prime d r c hd ?_ ?_⟩
    · simpa only [total, Nat.add_sub_cancel] using before
    · simpa only [total, Nat.add_sub_cancel] using fail
  intro bound
  induction bound with
  | zero => exact ⟨0, by omega, by simp [OeisA24356.a_0]⟩
  | succ b ih =>
    obtain ⟨n, ge, hn⟩ := ih
    obtain ⟨m, lt, hm⟩ := later n hn
    exact ⟨m, by omega, hm⟩

/-- A putative singularity gives either an affine dependence (forbidden
by H1) or an inhomogeneous solution. In the latter case H2 and a zero
coefficient in the new column produce a kernel vector at the next order. -/
lemma persistence (indep : H1) (extend : H2) {n : ℕ} (big : 5 ≤ n) (bad : OeisA24356.a n = 0) :
    OeisA24356.a (n + 1) = 0 := by
  classical
  obtain ⟨d, rfl⟩ : ∃ d, n = d + 1 := ⟨n - 1, by omega⟩
  have big' : 4 ≤ d := by omega
  let p (i : ℕ) : ℤ := Nat.nth Nat.Prime i
  let A : Matrix (Fin (d + 1)) (Fin (d + 1)) ℤ := Matrix.of fun i j => p (i.val + j.val)
  have singular : A.det = 0 := bad
  obtain ⟨c, nz, ker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr singular
  let b (j : Fin d) := c j.succ
  let s := -(c 0 + ∑ j, b j)
  let res (i : ℕ) := ∑ j, c j * p (i + j.val)
  let inc (i : ℕ) := ∑ j, b j * (p (i + j.val + 1) - p i)
  have difference (i : ℕ) : res i = inc i - s * p i := by
    dsimp only [res, inc, s]
    rw [Fin.sum_univ_succ]
    simp only [Fin.val_zero, Nat.add_zero, Fin.val_succ, ← Nat.add_assoc]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul]
    change _ + (∑ j, b j * p (i + j.val + 1)) = _
    ring
  have before (i : ℕ) (hi : i ≤ d) : inc i = s * p i := by
    apply sub_eq_zero.mp
    rw [← difference]
    have h := congrFun ker (⟨i, by omega⟩ : Fin (d + 1))
    simpa [A, res, p, Matrix.mulVec, dotProduct, mul_comm] using h
  have survives : s ≠ 0 := by
    intro zero
    have vanish := indep d big' b (fun i hi => by simpa only [zero, zero_mul] using before i hi)
    have head : c 0 = 0 := by simpa [s, vanish] using zero
    apply nz
    funext j
    exact Fin.cases head (fun t => congrFun vanish t) j
  have next : inc (d + 1) = s * p (d + 1) := extend d big' b s survives before
  have allRows (i : ℕ) (hi : i ≤ d + 1) : res i = 0 := by
    rw [difference]
    exact sub_eq_zero.mpr (if lt : i ≤ d then before i lt else (by rwa [show i = d + 1 by omega]))
  let y : Fin (d + 1 + 1) → ℤ := Fin.lastCases 0 c
  change (Matrix.of fun i j : Fin (d + 1 + 1) => p (i.val + j.val)).det = 0
  apply Matrix.exists_mulVec_eq_zero_iff.mp
  refine ⟨y, ?_, ?_⟩
  · intro h
    apply nz
    funext j
    simpa [y] using congrFun h j.castSucc
  · funext i
    change (∑ j, p (i.val + j.val) * y j) = 0
    rw [Fin.sum_univ_castSucc]
    simpa only [y, Fin.lastCases_castSucc, Fin.lastCases_last, mul_zero, zero_mul, add_zero,
      Fin.val_castSucc, res, mul_comm] using allRows i.val (by omega)

lemma third_nonzero : OeisA24356.a 3 ≠ 0 := by
  have eq : (Matrix.of fun (i j : Fin 3) => (Nat.nth Nat.Prime (i.val + j.val) : ℤ)) =
      !![(2 : ℤ), 3, 5; 3, 5, 7; 5, 7, 11] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Nat.nth_prime_zero_eq_two, Nat.nth_prime_one_eq_three,
      Nat.nth_prime_two_eq_five, Nat.nth_prime_three_eq_seven, Nat.nth_prime_four_eq_eleven]
  unfold OeisA24356.a
  rw [eq, Matrix.det_fin_three]
  decide

theorem main : H1 → H2 → OMA.R_OeisA24356_conjecture_R1.H2 := by
  intro indep extend n bad
  by_cases small : n < 5
  · interval_cases n <;> first | rfl | (exfalso; exact third_nonzero bad) |
      simp [OeisA24356.a_0, OeisA24356.a_1, OeisA24356.a_2] at bad
  have tail (t : ℕ) : OeisA24356.a (n + t) = 0 := by
    induction t with
    | zero => simpa using bad
    | succ t ih =>
      exact persistence indep extend (n := n + t) (le_trans (by omega : 5 ≤ n) (Nat.le_add_right n t)) ih
  obtain ⟨N, ge, hN⟩ := arbitrarily_large n
  exact (hN (by simpa only [show n + (N - n) = N by omega] using tail (N - n))).elim

end OMA.R_OeisA24356_conjecture_R1_H2_R1
