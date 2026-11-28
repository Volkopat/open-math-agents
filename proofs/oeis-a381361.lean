import OMAStatements.S_oeis_a381361
import Mathlib

/-!
# Proof of OEIS A381361 Conjecture

1. For any `f : ℕ → ℤ` and `m : ℕ`, the symmetric sum
   `∑ j : Fin (m + 1), C(m + 2, j + 1) * f (j + 1) * f (m + 1 - j)` is always even
   (pairing `k` with `m + 2 - k`, and using `2 ∣ C(2*r, r)` for `r >= 1` on the middle term).
   Hence the division by `2` in `a (m + 2)` is exact.
2. Define `v : ℕ → ZMod 5` taking `[1, 1, 3, 2, 1]` on `0..4` and `0` for `n >= 5`.
   By strong induction on `n`, `(a n : ZMod 5) = v n`:
   - For `m <= 16` (`n = m + 2 <= 18`), direct finite verification in `ZMod 5`.
   - For `m >= 17` (`n = m + 2 >= 19`), every term vanishes in `ZMod 5`,
     giving `2 * (a (m + 2) : ZMod 5) = 0`, hence `(a (m + 2) : ZMod 5) = 0`.
-/

namespace OeisA381361Proof

open Finset OMA.S_oeis_a381361

private lemma two_dvd_central_binom (k : ℕ) (hk : 1 ≤ k) : 2 ∣ Nat.choose (2 * k) k := by
  have h1 : 2 * k = (2 * k - 1) + 1 := by omega
  have h2 : k = (k - 1) + 1 := by omega
  have hch := Nat.add_one_mul_choose_eq (2 * k - 1) (k - 1)
  rw [← h1, ← h2] at hch
  have hmul : k * Nat.choose (2 * k) k = k * (2 * Nat.choose (2 * k - 1) (k - 1)) := by
    linarith
  have heq : Nat.choose (2 * k) k = 2 * Nat.choose (2 * k - 1) (k - 1) :=
    Nat.eq_of_mul_eq_mul_left (by omega : 0 < k) hmul
  exact ⟨Nat.choose (2 * k - 1) (k - 1), heq⟩

private lemma even_mid_sum (f : ℕ → ℤ) (m : ℕ) :
    (2 : ℤ) ∣ ∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ℤ) * f (j.1 + 1) * f (m + 1 - j.1) := by
  have hrew :
      (∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ℤ) * f (j.1 + 1) * f (m + 1 - j.1)) =
      ∑ k ∈ Finset.Icc 1 (m + 1), (Nat.choose (m + 2) k : ℤ) * f k * f (m + 2 - k) := by
    apply Finset.sum_bij (fun j _ => j.1 + 1)
    · intro j _; rw [Finset.mem_Icc]; have := j.2; omega
    · intro a _ b _ h; exact Fin.ext (by omega)
    · intro k hk; rw [Finset.mem_Icc] at hk
      refine ⟨⟨k - 1, by omega⟩, Finset.mem_univ _, by dsimp; omega⟩
    · intro j _; congr 1; congr 1; omega
  rw [hrew]
  set S := ∑ j ∈ Finset.Icc 1 (m + 1), (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j)
  have hsym : ∀ j ∈ Finset.Icc 1 (m + 1),
      (Nat.choose (m + 2) (m + 2 - j) : ℤ) * f (m + 2 - j) * f (m + 2 - (m + 2 - j)) =
      (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j) := by
    intro j hj
    rw [Finset.mem_Icc] at hj
    have hsub : m + 2 - (m + 2 - j) = j := by omega
    rw [hsub, Nat.choose_symm (by omega : j ≤ m + 2)]
    ring
  have hmod2 : (S : ZMod 2) = 0 := by
    let L := (Finset.Icc 1 (m + 1)).filter (fun j => 2 * j < m + 2)
    let R := (Finset.Icc 1 (m + 1)).filter (fun j => m + 2 < 2 * j)
    let M := (Finset.Icc 1 (m + 1)).filter (fun j => 2 * j = m + 2)
    have hpart : Finset.Icc 1 (m + 1) = L ∪ R ∪ M := by
      ext j
      simp only [L, R, M, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro hj
        rcases lt_trichotomy (2 * j) (m + 2) with h1 | h2 | h3
        · exact Or.inl (Or.inl ⟨hj, h1⟩)
        · exact Or.inr ⟨hj, h2⟩
        · exact Or.inl (Or.inr ⟨hj, h3⟩)
      · rintro ((⟨hj, _⟩ | ⟨hj, _⟩) | ⟨hj, _⟩) <;> exact hj
    have hLR : Disjoint L R := by
      rw [Finset.disjoint_left]; intro j h1 h2; simp only [L, R, Finset.mem_filter] at h1 h2; omega
    have hLRM : Disjoint (L ∪ R) M := by
      rw [Finset.disjoint_left]; intro j h1 h2
      simp only [L, R, M, Finset.mem_union, Finset.mem_filter] at h1 h2; omega
    have hS : S =
        (∑ j ∈ L, (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j)) +
        (∑ j ∈ R, (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j)) +
        (∑ j ∈ M, (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j)) := by
      change ∑ j ∈ Finset.Icc 1 (m + 1), _ = _
      rw [hpart, Finset.sum_union hLRM, Finset.sum_union hLR]
    have hReqL :
        (∑ j ∈ R, (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j)) =
        (∑ j ∈ L, (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j)) := by
      apply Finset.sum_bij (fun j _ => m + 2 - j)
      · intro j hj; simp only [R, L, Finset.mem_filter, Finset.mem_Icc] at hj ⊢; omega
      · intro a ha b hb hab; simp only [R, Finset.mem_filter, Finset.mem_Icc] at ha hb; omega
      · intro j hj; simp only [L, Finset.mem_filter, Finset.mem_Icc] at hj
        refine ⟨m + 2 - j, ?_, by omega⟩
        simp only [R, Finset.mem_filter, Finset.mem_Icc]; omega
      · intro j hj
        simp only [R, Finset.mem_filter] at hj
        exact (hsym j hj.1).symm
    have hM2 : (2 : ℤ) ∣ ∑ j ∈ M, (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j) := by
      apply Finset.dvd_sum
      intro j hj
      simp only [M, Finset.mem_filter, Finset.mem_Icc] at hj
      have h2j : m + 2 = 2 * j := by omega
      rw [h2j]
      have hd : (2 : ℤ) ∣ (Nat.choose (2 * j) j : ℤ) := by
        exact_mod_cast two_dvd_central_binom j (by omega)
      exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hd _) _
    rw [hS, hReqL]
    rcases hM2 with ⟨q, hq⟩
    rw [hq]
    set T : ℤ := ∑ j ∈ L, (Nat.choose (m + 2) j : ℤ) * f j * f (m + 2 - j)
    have h20 : (2 : ZMod 2) = 0 := by decide
    calc ((T + T + 2 * q : ℤ) : ZMod 2)
        = (2 : ZMod 2) * ((T : ZMod 2) + (q : ZMod 2)) := by push_cast; ring
      _ = 0 := by rw [h20, zero_mul]
  exact (ZMod.intCast_zmod_eq_zero_iff_dvd S 2).mp hmod2

private lemma two_mul_a_succ_succ (m : ℕ) :
    2 * a (m + 2) =
      8 * (∑ j : Fin (m + 1), (Nat.choose m j.1 : ℤ) *
            (∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ℤ) * a i.1 * a (j.1 - i.1)) *
            (∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ℤ) * a i.1 * a (m - j.1 - i.1))) -
      ∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ℤ) * a (j.1 + 1) * a (m + 1 - j.1) := by
  conv_lhs => unfold OMA.S_oeis_a381361.a
  have hdvd : (2 : ℤ) ∣
      8 * (∑ j : Fin (m + 1), (Nat.choose m j.1 : ℤ) *
            (∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ℤ) * a i.1 * a (j.1 - i.1)) *
            (∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ℤ) * a i.1 * a (m - j.1 - i.1))) -
      ∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ℤ) * a (j.1 + 1) * a (m + 1 - j.1) := by
    apply dvd_sub
    · exact dvd_mul_of_dvd_left (by decide : (2 : ℤ) ∣ 8) _
    · exact even_mid_sum a m
  exact Int.mul_ediv_cancel' hdvd

private def v : ℕ → ZMod 5
  | 0 => 1
  | 1 => 1
  | 2 => 3
  | 3 => 2
  | 4 => 1
  | _ + 5 => 0

private lemma v_eq_zero_of_gt_four {n : ℕ} (hn : 4 < n) : v n = 0 := by
  match n with
  | 0 | 1 | 2 | 3 | 4 => omega
  | _ + 5 => rfl

private lemma a_mod5_eq_v : ∀ n : ℕ, (a n : ZMod 5) = v n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    match n with
    | 0 => simp [OMA.S_oeis_a381361.a, v]
    | 1 => simp [OMA.S_oeis_a381361.a, v]
    | m + 2 =>
      have h2 := congrArg (Int.cast (R := ZMod 5)) (two_mul_a_succ_succ m)
      push_cast at h2
      have hA4 :
          (∑ j : Fin (m + 1), (Nat.choose m j.1 : ZMod 5) *
            (∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ZMod 5) * (a i.1 : ZMod 5) * (a (j.1 - i.1) : ZMod 5)) *
            (∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ZMod 5) * (a i.1 : ZMod 5) * (a (m - j.1 - i.1) : ZMod 5))) =
          (∑ j : Fin (m + 1), (Nat.choose m j.1 : ZMod 5) *
            (∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ZMod 5) * v i.1 * v (j.1 - i.1)) *
            (∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ZMod 5) * v i.1 * v (m - j.1 - i.1))) := by
        apply Finset.sum_congr rfl
        intro j _
        congr 1
        · congr 1
          apply Finset.sum_congr rfl
          intro i _
          have hj := j.2; have hi := i.2
          rw [ih i.1 (by omega), ih (j.1 - i.1) (by omega)]
        · apply Finset.sum_congr rfl
          intro i _
          have hj := j.2; have hi := i.2
          rw [ih i.1 (by omega), ih (m - j.1 - i.1) (by omega)]
      have hmid :
          (∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ZMod 5) * (a (j.1 + 1) : ZMod 5) * (a (m + 1 - j.1) : ZMod 5)) =
          (∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ZMod 5) * v (j.1 + 1) * v (m + 1 - j.1)) := by
        apply Finset.sum_congr rfl
        intro j _
        have hj := j.2
        rw [ih (j.1 + 1) (by omega), ih (m + 1 - j.1) (by omega)]
      rw [hA4, hmid] at h2
      have h2v : (2 : ZMod 5) * v (m + 2) =
          8 * (∑ j : Fin (m + 1), (Nat.choose m j.1 : ZMod 5) *
            (∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ZMod 5) * v i.1 * v (j.1 - i.1)) *
            (∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ZMod 5) * v i.1 * v (m - j.1 - i.1))) -
          ∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ZMod 5) * v (j.1 + 1) * v (m + 1 - j.1) := by
        by_cases hm : m ≤ 16
        · interval_cases m <;> decide
        · have hm17 : 17 ≤ m := by omega
          rw [v_eq_zero_of_gt_four (by omega), mul_zero]
          have hz1 : ∑ j : Fin (m + 1), (Nat.choose m j.1 : ZMod 5) *
              (∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ZMod 5) * v i.1 * v (j.1 - i.1)) *
              (∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ZMod 5) * v i.1 * v (m - j.1 - i.1)) = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            have hj := j.2
            by_cases hj9 : 9 ≤ j.1
            · have hs : ∑ i : Fin (j.1 + 1), (Nat.choose j.1 i.1 : ZMod 5) * v i.1 * v (j.1 - i.1) = 0 := by
                apply Finset.sum_eq_zero
                intro i _
                have hi := i.2
                by_cases hi5 : 4 < i.1
                · rw [v_eq_zero_of_gt_four hi5, mul_zero, zero_mul]
                · rw [v_eq_zero_of_gt_four (by omega : 4 < j.1 - i.1), mul_zero]
              rw [hs, mul_zero, zero_mul]
            · have hs : ∑ i : Fin (m - j.1 + 1), (Nat.choose (m - j.1) i.1 : ZMod 5) * v i.1 * v (m - j.1 - i.1) = 0 := by
                apply Finset.sum_eq_zero
                intro i _
                have hi := i.2
                by_cases hi5 : 4 < i.1
                · rw [v_eq_zero_of_gt_four hi5, mul_zero, zero_mul]
                · rw [v_eq_zero_of_gt_four (by omega : 4 < m - j.1 - i.1), mul_zero]
              rw [hs, mul_zero]
          have hz2 : ∑ j : Fin (m + 1), (Nat.choose (m + 2) (j.1 + 1) : ZMod 5) * v (j.1 + 1) * v (m + 1 - j.1) = 0 := by
            apply Finset.sum_eq_zero
            intro j _
            have hj := j.2
            by_cases hj5 : 4 < j.1 + 1
            · rw [v_eq_zero_of_gt_four hj5, mul_zero, zero_mul]
            · rw [v_eq_zero_of_gt_four (by omega : 4 < m + 1 - j.1), mul_zero]
          rw [hz1, hz2, mul_zero, sub_zero]
      have heq : (2 : ZMod 5) * (a (m + 2) : ZMod 5) = (2 : ZMod 5) * v (m + 2) := h2.trans h2v.symm
      have h32 : (3 : ZMod 5) * (2 : ZMod 5) = 1 := by decide
      calc (a (m + 2) : ZMod 5) = ((3 : ZMod 5) * 2) * (a (m + 2) : ZMod 5) := by rw [h32, one_mul]
        _ = (3 : ZMod 5) * ((2 : ZMod 5) * (a (m + 2) : ZMod 5)) := by ring
        _ = (3 : ZMod 5) * ((2 : ZMod 5) * v (m + 2)) := by rw [heq]
        _ = ((3 : ZMod 5) * 2) * v (m + 2) := by ring
        _ = v (m + 2) := by rw [h32, one_mul]

end OeisA381361Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a381361.main := by
  intro n hn
  change OMA.S_oeis_a381361.a n ≡ 0 [ZMOD ((5 : ℕ) : ℤ)]
  rw [← ZMod.intCast_eq_intCast_iff]
  rw [OeisA381361Proof.a_mod5_eq_v n, OeisA381361Proof.v_eq_zero_of_gt_four hn, Int.cast_zero]
