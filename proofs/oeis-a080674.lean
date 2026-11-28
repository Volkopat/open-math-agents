import OMAStatements.S_oeis_a080674

open Finset
-- Problem: A080674, numbers below 10^n whose decimal digits all lie in {6, 7, 8, 9}.
-- Credit: @OrangeHeadz
-- Original proof. Dropping the last digit is a bijection between the numbers counted for
-- n + 1 and pairs (a number below 10^n all of whose digits are at least 6, possibly 0; a last
-- digit in {6, 7, 8, 9}), which gives f (n + 1) = 4 * (f n + 1) and hence 3 * f n + 4 = 4^(n+1).

namespace OMA_A080674_Proof

/-- All decimal digits of `m` avoid 0, ..., 5 (true for `m = 0`, whose digit list is empty). -/
def Q (m : ℕ) : Prop := ∀ d ∈ Nat.digits 10 m, d ∉ ({0, 1, 2, 3, 4, 5} : Finset ℕ)

instance : DecidablePred Q := fun m => by unfold Q; infer_instance

theorem Q_zero : Q 0 := by
  intro d hd
  simp at hd

theorem Q_step (q d : ℕ) (hd : d < 10) (hpos : 0 < 10 * q + d) :
    Q (10 * q + d) ↔ d ∉ ({0, 1, 2, 3, 4, 5} : Finset ℕ) ∧ Q q := by
  unfold Q
  have h1 : (10 * q + d) % 10 = d := by omega
  have h2 : (10 * q + d) / 10 = q := by omega
  rw [Nat.digits_def' (by norm_num) hpos, h1, h2]
  simp only [List.mem_cons, forall_eq_or_imp]

/-- The numbers counted by the statement. -/
def S (n : ℕ) : Finset ℕ := (range (10 ^ n)).filter fun m => m ≠ 0 ∧ Q m

/-- The same numbers together with 0. -/
def T (n : ℕ) : Finset ℕ := (range (10 ^ n)).filter fun m => Q m

theorem card_T (n : ℕ) : (T n).card = (S n).card + 1 := by
  have h : T n = insert 0 (S n) := by
    ext m
    simp only [T, S, mem_filter, mem_range, mem_insert]
    constructor
    · rintro ⟨hm, hq⟩
      by_cases h0 : m = 0
      · exact Or.inl h0
      · exact Or.inr ⟨hm, h0, hq⟩
    · rintro (h0 | ⟨hm, -, hq⟩)
      · subst h0
        exact ⟨Nat.pow_pos (by norm_num), Q_zero⟩
      · exact ⟨hm, hq⟩
  rw [h, card_insert_of_notMem]
  simp [S]

theorem card_S_succ (n : ℕ) : (S (n + 1)).card = (T n).card * 4 := by
  rw [← show ({6, 7, 8, 9} : Finset ℕ).card = 4 from rfl, ← card_product]
  refine card_nbij' (fun m => (m / 10, m % 10)) (fun p => 10 * p.1 + p.2) ?_ ?_ ?_ ?_
  · intro m hm
    simp only [S, coe_filter, mem_range, Set.mem_ofPred_eq] at hm
    obtain ⟨hlt, hne, hq⟩ := hm
    have hdecomp : 10 * (m / 10) + m % 10 = m := Nat.div_add_mod m 10
    have hpos : 0 < 10 * (m / 10) + m % 10 := by omega
    have hq' : Q (10 * (m / 10) + m % 10) := by rw [hdecomp]; exact hq
    obtain ⟨hd, hrest⟩ := (Q_step (m / 10) (m % 10) (Nat.mod_lt _ (by norm_num)) hpos).mp hq'
    have hmod : m % 10 < 10 := Nat.mod_lt _ (by norm_num)
    simp only [coe_product, Set.mem_prod, mem_coe, T, mem_filter,
      mem_range]
    refine ⟨⟨?_, hrest⟩, ?_⟩
    · rw [pow_succ] at hlt
      omega
    · simp only [mem_insert, mem_singleton] at hd ⊢
      omega
  · rintro ⟨q, d⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe, T, mem_filter,
      mem_range, mem_insert, mem_singleton] at hp
    obtain ⟨⟨hq, hQ⟩, hd⟩ := hp
    have hd10 : d < 10 := by omega
    have hpos : 0 < 10 * q + d := by omega
    simp only [S, coe_filter, mem_range, Set.mem_ofPred_eq]
    refine ⟨?_, by omega, ?_⟩
    · rw [pow_succ]
      omega
    · refine (Q_step q d hd10 hpos).mpr ⟨?_, hQ⟩
      simp only [mem_insert, mem_singleton]
      omega
  · intro m _
    exact Nat.div_add_mod m 10
  · rintro ⟨q, d⟩ hp
    simp only [coe_product, Set.mem_prod, mem_coe, mem_insert,
      mem_singleton] at hp
    have hd10 : d < 10 := by omega
    refine Prod.ext ?_ ?_
    · show (10 * q + d) / 10 = q
      omega
    · show (10 * q + d) % 10 = d
      omega

theorem three_mul_card (n : ℕ) : 3 * (S n).card + 4 = 4 ^ (n + 1) := by
  induction n with
  | zero =>
    have h : S 0 = ∅ := by
      ext m
      simp only [S, mem_filter, mem_range, pow_zero, notMem_empty,
        iff_false]
      omega
    rw [h]
    simp
  | succ n ih =>
    rw [card_S_succ, card_T, pow_succ]
    omega

end OMA_A080674_Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a080674.main := by
  intro n
  have h := OMA_A080674_Proof.three_mul_card n
  have hS : ((range (10 ^ n)).filter fun m : ℕ =>
      m ≠ 0 ∧ ∀ d ∈ Nat.digits 10 m, d ∉ ({0, 1, 2, 3, 4, 5} : Finset ℕ)) =
      OMA_A080674_Proof.S n :=
    filter_congr (fun m _ => Iff.rfl)
  rw [hS]
  have hpos : 1 ≤ 4 ^ n := Nat.one_le_two_pow.trans (Nat.pow_le_pow_left (by norm_num) n)
  rw [pow_succ] at h
  omega
