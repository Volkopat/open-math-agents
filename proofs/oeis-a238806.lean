import OMAStatements.S_oeis_a238806
import Mathlib

namespace OMA.S_oeis_a238806

abbrev St := Fin 2 → Fin 3

def goodS {n : ℕ} (s : St) (x : Fin n → Fin 2 → Fin 3) : Prop :=
  ∀ i j, (x i j : ℕ) ≠ (1 + leftSum x i j) % 3 ∧ (x i j : ℕ) ≠ (1 + (s j : ℕ) + aboveSum x i j) % 3

instance {n : ℕ} (s : St) : DecidablePred (@goodS n s) := fun x => by unfold goodS; infer_instance

def rowOK (s r : St) : Prop :=
  (r 0 : ℕ) ≠ 1 ∧ (r 0 : ℕ) ≠ (1 + (s 0 : ℕ)) % 3 ∧
  (r 1 : ℕ) ≠ (1 + (r 0 : ℕ)) % 3 ∧ (r 1 : ℕ) ≠ (1 + (s 1 : ℕ)) % 3

instance (s r : St) : Decidable (rowOK s r) := by unfold rowOK; infer_instance

def R (s t : St) : Prop := rowOK s (t - s)
instance (s t : St) : Decidable (R s t) := by unfold R; infer_instance

def V : ℕ → St → ℕ
  | 0, _ => 1
  | n + 1, s => ∑ t, if R s t then V n t else 0

theorem goodS_mod {n : ℕ} (s s' : St) (h : ∀ j, (s j : ℕ) = s' j) (x : Fin n → Fin 2 → Fin 3) :
    goodS s x ↔ goodS s' x := by
  unfold goodS
  simp only [h]

theorem aboveSum_cons {n : ℕ} (r : Fin 2 → Fin 3) (y : Fin n → Fin 2 → Fin 3) (j : Fin 2) :
    aboveSum (Fin.cons r y : Fin (n + 1) → Fin 2 → Fin 3) 0 j = 0 ∧
    ∀ i : Fin n, aboveSum (Fin.cons r y : Fin (n + 1) → Fin 2 → Fin 3) i.succ j = (r j : ℕ) + aboveSum y i j := by
  constructor
  · simp [aboveSum]
  · intro i
    simp only [aboveSum, Finset.sum_filter, Fin.sum_univ_succ]
    simp

theorem goodS_cons {n : ℕ} (s r : St) (y : Fin n → Fin 2 → Fin 3) :
    goodS s (Fin.cons r y : Fin (n + 1) → Fin 2 → Fin 3) ↔ rowOK s r ∧ goodS (s + r) y := by
  have hA := fun j => aboveSum_cons r y j
  unfold goodS rowOK
  rw [Fin.forall_fin_succ]
  simp only [Fin.cons_zero, Fin.cons_succ, Fin.forall_fin_two]
  have l1 : ∀ i : Fin n, ∀ j, leftSum (Fin.cons r y : Fin (n + 1) → Fin 2 → Fin 3) i.succ j = leftSum y i j := by
    intro i j; simp [leftSum]
  have l0 : ∀ j, leftSum (Fin.cons r y : Fin (n + 1) → Fin 2 → Fin 3) 0 j = ∑ j' ∈ Finset.univ.filter (· < j), (r j' : ℕ) := by
    intro j; simp [leftSum]
  simp only [l1, l0, (hA 0).1, (hA 1).1, (hA 0).2, (hA 1).2]
  have e0 : ∑ j' ∈ Finset.univ.filter (· < (0 : Fin 2)), (r j' : ℕ) = 0 := by
    simp [Finset.sum_filter, Fin.sum_univ_two]
  have e1 : ∑ j' ∈ Finset.univ.filter (· < (1 : Fin 2)), (r j' : ℕ) = (r 0 : ℕ) := by
    simp [Finset.sum_filter, Fin.sum_univ_two]
  have h0 : ∀ A : ℕ, (1 + ((s 0 : ℕ) + (r 0 : ℕ)) % 3 + A) % 3 = (1 + (s 0 : ℕ) + ((r 0 : ℕ) + A)) % 3 := by
    intro A; omega
  have h1 : ∀ A : ℕ, (1 + ((s 1 : ℕ) + (r 1 : ℕ)) % 3 + A) % 3 = (1 + (s 1 : ℕ) + ((r 1 : ℕ) + A)) % 3 := by
    intro A; omega
  simp only [e0, e1, Pi.add_apply, Fin.val_add, h0, h1, add_zero]
  tauto

theorem cardS (n : ℕ) : ∀ s : St,
    ((Finset.univ : Finset (Fin n → Fin 2 → Fin 3)).filter (goodS s)).card = V n s := by
  induction n with
  | zero =>
    intro s
    simp only [V]
    rw [Finset.card_eq_one]
    refine ⟨fun i => i.elim0, ?_⟩
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
    constructor
    · intro _; funext i; exact i.elim0
    · intro _ i; exact i.elim0
  | succ n ih =>
    intro s
    rw [← Fintype.card_subtype]
    let e : {x : Fin (n + 1) → Fin 2 → Fin 3 // goodS s x} ≃
        {z : (Fin 2 → Fin 3) × (Fin n → Fin 2 → Fin 3) //
          goodS s (Fin.cons z.1 z.2 : Fin (n + 1) → Fin 2 → Fin 3)} :=
      Equiv.subtypeEquiv (Fin.consEquiv (fun _ => Fin 2 → Fin 3)).symm (by
        intro x
        show goodS s x ↔ goodS s (Fin.cons (x 0) (Fin.tail x) : Fin (n + 1) → Fin 2 → Fin 3)
        rw [Fin.cons_self_tail])
    let e2 := e.trans (Equiv.subtypeProdEquivSigmaSubtype
      (fun (r : Fin 2 → Fin 3) (y : Fin n → Fin 2 → Fin 3) =>
        goodS s (Fin.cons r y : Fin (n + 1) → Fin 2 → Fin 3)))
    rw [Fintype.card_congr e2, Fintype.card_sigma]
    simp only [V]
    rw [← (Equiv.subRight s).sum_comp]
    apply Finset.sum_congr rfl
    intro r _
    have hr : s + (Equiv.subRight s) r = r := by
      simp [Equiv.subRight]
    have hc : ∀ b : Fin n → Fin 2 → Fin 3,
        goodS s (Fin.cons ((Equiv.subRight s) r) b : Fin (n + 1) → Fin 2 → Fin 3) ↔
          R s r ∧ goodS r b := by
      intro b
      rw [goodS_cons, hr]
      rfl
    by_cases h : R s r
    · rw [if_pos h]
      rw [← ih r, ← Fintype.card_subtype]
      apply Fintype.card_congr
      exact Equiv.subtypeEquivRight (fun b => by rw [hc]; simp [h])
    · rw [if_neg h]
      rw [Fintype.card_eq_zero_iff]
      refine ⟨fun b => ?_⟩
      exact h ((hc b.1).1 b.2).1

theorem a_eq (n : ℕ) : a n = V n 0 := by
  rw [← cardS n 0]
  unfold a
  congr 1

def cc : ℕ → ℤ := fun j => [(1 : ℤ), -4, 6, -4, 1].getD j 0

theorem rec_gen (n : ℕ) : ∀ s : St, ∑ j ∈ Finset.range 5, cc j * (V (n + 1 + j) s : ℤ) = 0 := by
  induction n with
  | zero =>
    intro s
    revert s
    decide +kernel
  | succ n ih =>
    intro s
    have : ∀ j, (V (n + 1 + 1 + j) s : ℤ) = ∑ t, if R s t then (V (n + 1 + j) t : ℤ) else 0 := by
      intro j
      rw [show n + 1 + 1 + j = (n + 1 + j) + 1 by omega]
      simp [V]
    simp only [this, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro t _
    by_cases h : R s t
    · have := ih t
      simp only [h, if_true]
      simpa [← Finset.mul_sum] using this
    · simp [h]

theorem hrec (n : ℕ) : (a (n + 5) : ℤ) = 4 * a (n + 4) - 6 * a (n + 3) + 4 * a (n + 2) - a (n + 1) := by
  have h := rec_gen n 0
  simp only [Finset.sum_range_succ, Finset.sum_range_zero] at h
  simp only [cc, List.getD_cons_zero, List.getD_cons_succ] at h
  simp only [a_eq]
  simp only [Nat.add_assoc, Nat.reduceAdd] at h
  push_cast at h
  linarith

end OMA.S_oeis_a238806

open PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a238806.main := by
  open OMA.S_oeis_a238806 in
  have a1 : a 1 = 3 := by rw [a_eq]; decide +kernel
  open OMA.S_oeis_a238806 in
  have a2 : a 2 = 8 := by rw [a_eq]; decide +kernel
  open OMA.S_oeis_a238806 in
  have a3 : a 3 = 15 := by rw [a_eq]; decide +kernel
  open OMA.S_oeis_a238806 in
  have a4 : a 4 = 25 := by rw [a_eq]; decide +kernel
  constructor
  · have hp : ((1 : PowerSeries ℚ) - X) ^ 4 = 1 - 4 * X + 6 * X ^ 2 - 4 * X ^ 3 + X ^ 4 := by ring
    rw [hp]
    ext n
    have n3 : (3 : PowerSeries ℚ) = PowerSeries.C 3 := (map_ofNat (PowerSeries.C) 3).symm
    have n4 : (4 : PowerSeries ℚ) = PowerSeries.C 4 := (map_ofNat (PowerSeries.C) 4).symm
    have n6 : (6 : PowerSeries ℚ) = PowerSeries.C 6 := (map_ofNat (PowerSeries.C) 6).symm
    have n8 : (8 : PowerSeries ℚ) = PowerSeries.C 8 := (map_ofNat (PowerSeries.C) 8).symm
    rw [n3, n4, n6]
    have hf : ∀ f : PowerSeries ℚ, f * (1 - PowerSeries.C 4 * X + PowerSeries.C 6 * X ^ 2 - PowerSeries.C 4 * X ^ 3 + X ^ 4) =
        f - PowerSeries.C 4 * (f * X ^ 1) + PowerSeries.C 6 * (f * X ^ 2) - PowerSeries.C 4 * (f * X ^ 3) + f * X ^ 4 := by
      intro f; ring
    rw [hf]
    have hr : ∀ m : ℕ, ((a (m + 5) : ℚ) - 4 * a (m + 4) + 6 * a (m + 3) - 4 * a (m + 2) + a (m + 1)) = 0 := by
      intro m
      have := hrec m
      have h' : ((a (m + 5) : ℤ) : ℚ) = ((4 * a (m + 4) - 6 * a (m + 3) + 4 * a (m + 2) - a (m + 1) : ℤ) : ℚ) := by
        rw [this]
      push_cast at h'
      linarith
    simp only [map_sub, map_add, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_X_pow', PowerSeries.coeff_mk]
    rcases n with _ | _ | _ | _ | n
    · simp [a1]
    · simp [a1, a2, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one]; norm_num
    · simp [a1, a2, a3, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one]; norm_num
    · simp [a1, a2, a3, a4, PowerSeries.coeff_X_pow, PowerSeries.coeff_X, PowerSeries.coeff_one]; norm_num
    · have := hr n
      simp [PowerSeries.coeff_X_pow, PowerSeries.coeff_X]
      exact this
  · intro n hn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 5 := ⟨n - 5, by omega⟩
    have := OMA.S_oeis_a238806.hrec m
    simpa using this
