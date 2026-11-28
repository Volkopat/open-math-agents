import OMAStatements.S_oeis_a345754
import Mathlib

open OMA.S_oeis_a345754

namespace P345754

open Finset

theorem per2 {R : Type*} [CommRing R] (M : Matrix (Fin 2) (Fin 2) R) :
    M.permanent = M 0 0 * M 1 1 + M 0 1 * M 1 0 := by
  rw [Matrix.permanent]
  rw [show (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} by decide]
  rw [Finset.sum_pair (by decide)]
  simp [Fin.prod_univ_two]
  ring

theorem step1 (n : ℕ) [NeZero n] :
    a n = Fintype.card {M : Matrix (Fin 2) (Fin 2) (ZMod n) // 2 * M 0 1 * M 1 0 = 0} := by
  rw [a, Fintype.card_subtype]
  congr 1
  apply Finset.filter_congr
  intro M _
  rw [per2, Matrix.det_fin_two]
  constructor
  · intro h; linear_combination h
  · intro h; linear_combination h

def eqv (n : ℕ) : {M : Matrix (Fin 2) (Fin 2) (ZMod n) // 2 * M 0 1 * M 1 0 = 0} ≃
    (ZMod n × ZMod n) × {p : ZMod n × ZMod n // 2 * p.1 * p.2 = 0} where
  toFun M := ((M.1 0 0, M.1 1 1), ⟨(M.1 0 1, M.1 1 0), M.2⟩)
  invFun x := ⟨!![x.1.1, x.2.1.1; x.2.1.2, x.1.2], by simpa using x.2.2⟩
  left_inv M := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> rfl
  right_inv x := rfl

theorem step2 (n : ℕ) [NeZero n] :
    a n = n ^ 2 * Fintype.card {p : ZMod n × ZMod n // 2 * p.1 * p.2 = 0} := by
  rw [step1, Fintype.card_congr (eqv n), Fintype.card_prod, Fintype.card_prod, ZMod.card]
  ring

theorem count_mul (n : ℕ) [NeZero n] (m : ℕ) :
    (univ.filter (fun c : ZMod n => (m : ZMod n) * c = 0)).card = Nat.gcd m n := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  set g := Nat.gcd m n with hg
  have hg0 : 0 < g := Nat.gcd_pos_of_pos_right m hn
  obtain ⟨n', hn'⟩ : g ∣ n := Nat.gcd_dvd_right m n
  obtain ⟨m', hm'⟩ : g ∣ m := Nat.gcd_dvd_left m n
  have hcop : Nat.Coprime m' n' := by
    have := Nat.coprime_div_gcd_div_gcd (m := m) (n := n) hg0
    rw [← hg] at this
    have e1 : m / g = m' := by rw [hm']; exact Nat.mul_div_cancel_left m' hg0
    have e2 : n / g = n' := by rw [hn']; exact Nat.mul_div_cancel_left n' hg0
    rwa [e1, e2] at this
  have hn'0 : 0 < n' := by rcases Nat.eq_zero_or_pos n' with h | h <;> [simp [h] at hn'; exact h] <;> omega
  -- transport to range n
  have h1 : (univ.filter (fun c : ZMod n => (m : ZMod n) * c = 0)).card =
      ((range n).filter (fun k => n' ∣ k)).card := by
    apply Finset.card_nbij' (fun c : ZMod n => c.val) (fun k : ℕ => (k : ZMod n))
    · intro c hc
      simp only [mem_filter, mem_univ, true_and, mem_coe] at hc ⊢
      refine ⟨mem_range.mpr (ZMod.val_lt c), ?_⟩
      have : ((m * c.val : ℕ) : ZMod n) = 0 := by push_cast; rw [ZMod.natCast_zmod_val]; exact hc
      rw [ZMod.natCast_eq_zero_iff] at this
      have key : ∀ v : ℕ, n ∣ m * v → n' ∣ v := by
        intro v hv
        rw [hn', hm', mul_assoc] at hv
        exact hcop.symm.dvd_of_dvd_mul_left (Nat.dvd_of_mul_dvd_mul_left hg0 hv)
      exact key _ this
    · intro k hk
      simp only [mem_filter, mem_univ, true_and, mem_coe, mem_range] at hk ⊢
      obtain ⟨hk1, t, rfl⟩ := hk
      rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff, hn', hm']
      exact ⟨m' * t, by ring⟩
    · intro c _; exact ZMod.natCast_zmod_val c
    · intro k hk
      have hk' : k < n := mem_range.mp (mem_filter.mp (mem_coe.mp hk)).1
      simp [ZMod.val_cast_of_lt hk']
  rw [h1]
  have h2 : (range n).filter (fun k => n' ∣ k) = (range g).image (fun t => n' * t) := by
    ext k
    simp only [mem_filter, mem_range, mem_image]
    constructor
    · rintro ⟨hk, t, rfl⟩
      refine ⟨t, ?_, rfl⟩
      rw [hn'] at hk
      by_contra hcon
      have : g * n' ≤ n' * t := by nlinarith
      omega
    · rintro ⟨t, ht, rfl⟩
      refine ⟨?_, dvd_mul_right _ _⟩
      rw [hn']
      nlinarith
  rw [h2, card_image_of_injective _ (fun u v h => Nat.eq_of_mul_eq_mul_left hn'0 h), card_range]

theorem step3 (n : ℕ) [NeZero n] :
    Fintype.card {p : ZMod n × ZMod n // 2 * p.1 * p.2 = 0} =
      ∑ b : ZMod n, Nat.gcd (2 * b.val) n := by
  rw [Fintype.card_subtype, card_filter, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro b _
  rw [← card_filter, ← count_mul n (2 * b.val)]
  congr 1
  apply Finset.filter_congr
  intro c _
  push_cast
  rw [ZMod.natCast_zmod_val]

theorem step4 (n : ℕ) [NeZero n] :
    ∑ b : ZMod n, Nat.gcd (2 * b.val) n = A344372 n := by
  have h1 : ∑ b : ZMod n, Nat.gcd (2 * b.val) n = ∑ k ∈ range n, Nat.gcd (2 * k) n := by
    apply Finset.sum_nbij' (fun c : ZMod n => c.val) (fun k : ℕ => (k : ZMod n))
    · intro c _; simp [ZMod.val_lt c]
    · intro k _; simp
    · intro c _; exact ZMod.natCast_zmod_val c
    · intro k hk
      simp only [mem_range] at hk
      simp [ZMod.val_cast_of_lt hk]
    · intro c _; rfl
  rw [h1, A344372]
  have hgen : ∀ (f : ℕ → ℕ) (N : ℕ), ∑ k ∈ Icc 1 N, f k = ∑ k ∈ range N, f (k + 1) := by
    intro f N
    induction N with
    | zero => simp
    | succ N ih => rw [Finset.sum_Icc_succ_top (by omega), ih, Finset.sum_range_succ]
  have h2 := hgen (fun k => Nat.gcd (2 * k) n) n
  rw [h2]
  have e1 := Finset.sum_range_succ (fun k => Nat.gcd (2 * k) n) n
  have e2 := Finset.sum_range_succ' (fun k => Nat.gcd (2 * k) n) n
  have e3 : Nat.gcd (2 * n) n = Nat.gcd (2 * 0) n := by simp
  omega

end P345754

theorem OMA.solution : type_of% @OMA.S_oeis_a345754.main := by
  intro n _
  rw [P345754.step2, P345754.step3, P345754.step4, mul_comm]
