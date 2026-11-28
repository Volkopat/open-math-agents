import OMAStatements.S_oeis_a064671

namespace OMA.P_a064671

open OMA.S_oeis_a064671
open Classical

/-- Number of positions in `S` holding the digit `d`. -/
def cS {n : ℕ} (S : Finset (Fin n)) (d : ℕ) (f : Fin n → Fin 4) : ℕ :=
  ∑ i ∈ S, if (f i : ℕ) = d then 1 else 0

/-- Number of positions holding the digit `d`. -/
def cnt {n : ℕ} (d : ℕ) (f : Fin n → Fin 4) : ℕ := cS Finset.univ d f

/-- Number of strings whose digit counts `(#1, #2, #3)` satisfy `Q`. -/
noncomputable def N (n : ℕ) (Q : ℕ → ℕ → ℕ → Prop) : ℕ :=
  ∑ f : Fin n → Fin 4, if Q (cnt 1 f) (cnt 2 f) (cnt 3 f) then 1 else 0

lemma N_congr {n : ℕ} {Q Q' : ℕ → ℕ → ℕ → Prop} (h : ∀ a b c, Q a b c ↔ Q' a b c) :
    N n Q = N n Q' := by
  have : Q = Q' := funext fun a => funext fun b => funext fun c => propext (h a b c)
  rw [this]

def pF (a _ _ : ℕ) : Prop := a + 1 = 0

lemma N_false (n : ℕ) : N n pF = 0 := by
  simp [N, pF]

lemma N_zero (Q : ℕ → ℕ → ℕ → Prop) : N 0 Q = if Q 0 0 0 then 1 else 0 := by
  simp [N, cnt, cS]

lemma N_split (n : ℕ) (Q R : ℕ → ℕ → ℕ → Prop) :
    N n Q = N n (fun a b c => Q a b c ∧ R a b c) + N n (fun a b c => Q a b c ∧ ¬ R a b c) := by
  simp only [N, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun f _ => ?_)
  by_cases h1 : Q (cnt 1 f) (cnt 2 f) (cnt 3 f) <;>
    by_cases h2 : R (cnt 1 f) (cnt 2 f) (cnt 3 f) <;> simp [h1, h2]

lemma cnt_cons {n : ℕ} (d : ℕ) (x : Fin 4) (g : Fin n → Fin 4) :
    cnt d (Fin.cons x g : Fin (n + 1) → Fin 4) = cnt d g + if (x : ℕ) = d then 1 else 0 := by
  simp only [cnt, cS, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  ring

lemma N_succ (n : ℕ) (Q : ℕ → ℕ → ℕ → Prop) :
    N (n + 1) Q = N n Q + N n (fun a b c => Q (a + 1) b c) + N n (fun a b c => Q a (b + 1) c) +
      N n (fun a b c => Q a b (c + 1)) := by
  rw [N, ← (Fin.consEquiv (fun _ : Fin (n + 1) => Fin 4)).sum_comp, Fintype.sum_prod_type,
    Fin.sum_univ_four]
  simp only [Fin.consEquiv, Equiv.coe_fn_mk, cnt_cons]
  simp [N]

lemma N_succ' (n : ℕ) (Q Q0 Q1 Q2 Q3 : ℕ → ℕ → ℕ → Prop)
    (h0 : ∀ a b c, Q a b c ↔ Q0 a b c) (h1 : ∀ a b c, Q (a + 1) b c ↔ Q1 a b c)
    (h2 : ∀ a b c, Q a (b + 1) c ↔ Q2 a b c) (h3 : ∀ a b c, Q a b (c + 1) ↔ Q3 a b c) :
    N (n + 1) Q = N n Q0 + N n Q1 + N n Q2 + N n Q3 := by
  rw [N_succ, N_congr h0, N_congr h1, N_congr h2, N_congr h3]

lemma N_true (n : ℕ) : N n (fun _ _ _ => True) = 4 ^ n := by
  induction n with
  | zero => simp [N_zero]
  | succ n ih =>
    rw [N_succ' n _ (fun _ _ _ => True) (fun _ _ _ => True) (fun _ _ _ => True)
      (fun _ _ _ => True) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl) (fun _ _ _ => Iff.rfl)
      (fun _ _ _ => Iff.rfl), ih]
    ring

lemma N_compl (n : ℕ) (R : ℕ → ℕ → ℕ → Prop) :
    N n R + N n (fun a b c => ¬ R a b c) = 4 ^ n := by
  rw [← N_true n, N_split n (fun _ _ _ => True) R]
  simp only [true_and]

def pEv (a _ c : ℕ) : Prop := (a + c) % 2 = 0
def pOd (a _ c : ℕ) : Prop := ¬ (a + c) % 2 = 0
def pZ (a b c : ℕ) : Prop := a = 0 ∧ b = 0 ∧ c = 0
def pB1 (a b c : ℕ) : Prop := a = 0 ∧ c = 0 ∧ b % 2 = 1
def pB1e (a b c : ℕ) : Prop := a = 0 ∧ c = 0 ∧ b % 2 = 0
def pC0 (a b c : ℕ) : Prop := a = 0 ∧ b = 0 ∧ c % 2 = 0
def pC1 (a b c : ℕ) : Prop := a = 0 ∧ b = 0 ∧ c % 2 = 1
def pB3 (a b c : ℕ) : Prop := b = 0 ∧ a = 1 ∧ c % 2 = 1
def pB3e (a b c : ℕ) : Prop := b = 0 ∧ a = 1 ∧ c % 2 = 0
def pD0 (a b c : ℕ) : Prop := a = 0 ∧ b = 1 ∧ c % 2 = 0
def pD1 (a b c : ℕ) : Prop := a = 0 ∧ b = 1 ∧ c % 2 = 1
def pY (a b c : ℕ) : Prop := a = 0 ∧ b = 1 ∧ c = 0
def pB2 (a b c : ℕ) : Prop := a = 0 ∧ b = 1 ∧ c % 2 = 0 ∧ 2 ≤ c
def pSpl (a b c : ℕ) : Prop :=
  a + b + c ≠ 0 ∧ (a + c) % 2 = 0 ∧ ¬ (a = 0 ∧ c = 0 ∧ b % 2 = 1) ∧
    ¬ (a = 0 ∧ b = 1 ∧ c % 2 = 0 ∧ 2 ≤ c) ∧ ¬ (b = 0 ∧ a = 1 ∧ c % 2 = 1)

lemma N_ev (n : ℕ) : N (n + 1) pEv = 2 * 4 ^ n := by
  have h := N_compl n pEv
  rw [N_succ' n pEv pEv pOd pEv pOd (fun a b c => by simp only [pEv, pOd] <;> omega)
    (fun a b c => by simp only [pEv, pOd] <;> omega) (fun a b c => by simp only [pEv, pOd] <;> omega)
    (fun a b c => by simp only [pEv, pOd] <;> omega)]
  have e : N n pOd = N n (fun a b c => ¬ pEv a b c) := N_congr (fun a b c => Iff.rfl)
  omega

lemma N_Z (n : ℕ) : N n pZ = 1 := by
  induction n with
  | zero => simp [N_zero, pZ]
  | succ n ih =>
    rw [N_succ' n pZ pZ pF pF pF (fun a b c => by simp only [pZ, pF] <;> omega)
      (fun a b c => by simp only [pZ, pF] <;> omega) (fun a b c => by simp only [pZ, pF] <;> omega)
      (fun a b c => by simp only [pZ, pF] <;> omega), ih, N_false]

lemma N_B1 (n : ℕ) : N (n + 1) pB1 = 2 ^ n ∧ N (n + 1) pB1e = 2 ^ n := by
  have r1 : ∀ m, N (m + 1) pB1 = N m pB1 + N m pB1e := by
    intro m
    rw [N_succ' m pB1 pB1 pF pB1e pF (fun a b c => by simp only [pB1, pB1e, pF] <;> omega)
      (fun a b c => by simp only [pB1, pB1e, pF] <;> omega)
      (fun a b c => by simp only [pB1, pB1e, pF] <;> omega)
      (fun a b c => by simp only [pB1, pB1e, pF] <;> omega), N_false]
    ring
  have r2 : ∀ m, N (m + 1) pB1e = N m pB1e + N m pB1 := by
    intro m
    rw [N_succ' m pB1e pB1e pF pB1 pF (fun a b c => by simp only [pB1, pB1e, pF] <;> omega)
      (fun a b c => by simp only [pB1, pB1e, pF] <;> omega)
      (fun a b c => by simp only [pB1, pB1e, pF] <;> omega)
      (fun a b c => by simp only [pB1, pB1e, pF] <;> omega), N_false]
    ring
  induction n with
  | zero => rw [r1 0, r2 0]; simp [N_zero, pB1, pB1e]
  | succ n ih => rw [r1 (n + 1), r2 (n + 1), ih.1, ih.2]; constructor <;> ring

lemma N_C (n : ℕ) : N (n + 1) pC0 = 2 ^ n ∧ N (n + 1) pC1 = 2 ^ n := by
  have r1 : ∀ m, N (m + 1) pC0 = N m pC0 + N m pC1 := by
    intro m
    rw [N_succ' m pC0 pC0 pF pF pC1 (fun a b c => by simp only [pC0, pC1, pF] <;> omega)
      (fun a b c => by simp only [pC0, pC1, pF] <;> omega)
      (fun a b c => by simp only [pC0, pC1, pF] <;> omega)
      (fun a b c => by simp only [pC0, pC1, pF] <;> omega), N_false]
    ring
  have r2 : ∀ m, N (m + 1) pC1 = N m pC1 + N m pC0 := by
    intro m
    rw [N_succ' m pC1 pC1 pF pF pC0 (fun a b c => by simp only [pC0, pC1, pF] <;> omega)
      (fun a b c => by simp only [pC0, pC1, pF] <;> omega)
      (fun a b c => by simp only [pC0, pC1, pF] <;> omega)
      (fun a b c => by simp only [pC0, pC1, pF] <;> omega), N_false]
    ring
  induction n with
  | zero => rw [r1 0, r2 0]; simp [N_zero, pC0, pC1]
  | succ n ih => rw [r1 (n + 1), r2 (n + 1), ih.1, ih.2]; constructor <;> ring

lemma N_C0_zero : N 0 pC0 = 1 := by simp [N_zero, pC0]
lemma N_C1_zero : N 0 pC1 = 0 := by simp [N_zero, pC1]

lemma N_B3 (n : ℕ) : N (n + 2) pB3 = (n + 2) * 2 ^ n ∧ N (n + 2) pB3e = (n + 2) * 2 ^ n := by
  have r1 : ∀ m, N (m + 1) pB3 = N m pB3 + N m pC1 + N m pB3e := by
    intro m
    rw [N_succ' m pB3 pB3 pC1 pF pB3e (fun a b c => by simp only [pB3, pB3e, pC1, pF] <;> omega)
      (fun a b c => by simp only [pB3, pB3e, pC1, pF] <;> omega)
      (fun a b c => by simp only [pB3, pB3e, pC1, pF] <;> omega)
      (fun a b c => by simp only [pB3, pB3e, pC1, pF] <;> omega), N_false]
    ring
  have r2 : ∀ m, N (m + 1) pB3e = N m pB3e + N m pC0 + N m pB3 := by
    intro m
    rw [N_succ' m pB3e pB3e pC0 pF pB3 (fun a b c => by simp only [pB3, pB3e, pC0, pF] <;> omega)
      (fun a b c => by simp only [pB3, pB3e, pC0, pF] <;> omega)
      (fun a b c => by simp only [pB3, pB3e, pC0, pF] <;> omega)
      (fun a b c => by simp only [pB3, pB3e, pC0, pF] <;> omega), N_false]
    ring
  induction n with
  | zero =>
    show N (0 + 1 + 1) pB3 = (0 + 2) * 2 ^ 0 ∧ N (0 + 1 + 1) pB3e = (0 + 2) * 2 ^ 0
    rw [r1 (0 + 1), r2 (0 + 1), r1 0, r2 0, (N_C 0).1, (N_C 0).2, N_C0_zero, N_C1_zero]
    simp [N_zero, pB3, pB3e]
  | succ n ih =>
    have hC0 : N (n + 2) pC0 = 2 ^ (n + 1) := (N_C (n + 1)).1
    have hC1 : N (n + 2) pC1 = 2 ^ (n + 1) := (N_C (n + 1)).2
    show N (n + 2 + 1) pB3 = (n + 1 + 2) * 2 ^ (n + 1) ∧
      N (n + 2 + 1) pB3e = (n + 1 + 2) * 2 ^ (n + 1)
    rw [r1 (n + 2), r2 (n + 2), ih.1, ih.2, hC0, hC1]
    constructor <;> ring

lemma N_D (n : ℕ) : N (n + 2) pD0 = (n + 2) * 2 ^ n := by
  have r1 : ∀ m, N (m + 1) pD1 = N m pD1 + N m pC1 + N m pD0 := by
    intro m
    rw [N_succ' m pD1 pD1 pF pC1 pD0 (fun a b c => by simp only [pD0, pD1, pC1, pF] <;> omega)
      (fun a b c => by simp only [pD0, pD1, pC1, pF] <;> omega)
      (fun a b c => by simp only [pD0, pD1, pC1, pF] <;> omega)
      (fun a b c => by simp only [pD0, pD1, pC1, pF] <;> omega), N_false]
    ring
  have r2 : ∀ m, N (m + 1) pD0 = N m pD0 + N m pC0 + N m pD1 := by
    intro m
    rw [N_succ' m pD0 pD0 pF pC0 pD1 (fun a b c => by simp only [pD0, pD1, pC0, pF] <;> omega)
      (fun a b c => by simp only [pD0, pD1, pC0, pF] <;> omega)
      (fun a b c => by simp only [pD0, pD1, pC0, pF] <;> omega)
      (fun a b c => by simp only [pD0, pD1, pC0, pF] <;> omega), N_false]
    ring
  have key : ∀ n, N (n + 2) pD1 = (n + 2) * 2 ^ n ∧ N (n + 2) pD0 = (n + 2) * 2 ^ n := by
    intro n
    induction n with
    | zero =>
      show N (0 + 1 + 1) pD1 = (0 + 2) * 2 ^ 0 ∧ N (0 + 1 + 1) pD0 = (0 + 2) * 2 ^ 0
      rw [r1 (0 + 1), r2 (0 + 1), r1 0, r2 0, (N_C 0).1, (N_C 0).2, N_C0_zero, N_C1_zero]
      simp [N_zero, pD0, pD1]
    | succ n ih =>
      have hC0 : N (n + 2) pC0 = 2 ^ (n + 1) := (N_C (n + 1)).1
      have hC1 : N (n + 2) pC1 = 2 ^ (n + 1) := (N_C (n + 1)).2
      show N (n + 2 + 1) pD1 = (n + 1 + 2) * 2 ^ (n + 1) ∧
        N (n + 2 + 1) pD0 = (n + 1 + 2) * 2 ^ (n + 1)
      rw [r1 (n + 2), r2 (n + 2), ih.1, ih.2, hC0, hC1]
      constructor <;> ring
  exact (key n).2

lemma N_Y (n : ℕ) : N n pY = n := by
  induction n with
  | zero => simp [N_zero, pY]
  | succ n ih =>
    rw [N_succ' n pY pY pF pZ pF (fun a b c => by simp only [pY, pZ, pF] <;> omega)
      (fun a b c => by simp only [pY, pZ, pF] <;> omega) (fun a b c => by simp only [pY, pZ, pF] <;> omega)
      (fun a b c => by simp only [pY, pZ, pF] <;> omega), ih, N_false, N_Z]

lemma N_spl (n : ℕ) (hn : 2 ≤ n) :
    2 * (N n pSpl : ℤ) = (2 ^ n - 2) * (1 + 2 ^ n - n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  have s1 := N_split (m + 2) pEv pSpl
  have c1 : N (m + 2) (fun a b c => pEv a b c ∧ pSpl a b c) = N (m + 2) pSpl :=
    N_congr (fun a b c => by simp only [pEv, pSpl] <;> omega)
  have s2 := N_split (m + 2) (fun a b c => pEv a b c ∧ ¬ pSpl a b c) pZ
  have c2 : N (m + 2) (fun a b c => (pEv a b c ∧ ¬ pSpl a b c) ∧ pZ a b c) = N (m + 2) pZ :=
    N_congr (fun a b c => by simp only [pEv, pSpl, pZ] <;> omega)
  have s3 := N_split (m + 2) (fun a b c => (pEv a b c ∧ ¬ pSpl a b c) ∧ ¬ pZ a b c) pB1
  have c3 : N (m + 2) (fun a b c => ((pEv a b c ∧ ¬ pSpl a b c) ∧ ¬ pZ a b c) ∧ pB1 a b c) =
      N (m + 2) pB1 :=
    N_congr (fun a b c => by simp only [pEv, pSpl, pZ, pB1] <;> omega)
  have s4 := N_split (m + 2)
    (fun a b c => ((pEv a b c ∧ ¬ pSpl a b c) ∧ ¬ pZ a b c) ∧ ¬ pB1 a b c) pB3
  have c4 : N (m + 2)
      (fun a b c => (((pEv a b c ∧ ¬ pSpl a b c) ∧ ¬ pZ a b c) ∧ ¬ pB1 a b c) ∧ pB3 a b c) =
      N (m + 2) pB3 :=
    N_congr (fun a b c => by simp only [pEv, pSpl, pZ, pB1, pB3] <;> omega)
  have c5 : N (m + 2)
      (fun a b c => (((pEv a b c ∧ ¬ pSpl a b c) ∧ ¬ pZ a b c) ∧ ¬ pB1 a b c) ∧ ¬ pB3 a b c) =
      N (m + 2) (fun a b c => pD0 a b c ∧ 2 ≤ c) :=
    N_congr (fun a b c => by simp only [pEv, pSpl, pZ, pB1, pB3, pD0] <;> omega)
  have s5 := N_split (m + 2) pD0 (fun _ _ c => 2 ≤ c)
  have c6 : N (m + 2) (fun a b c => pD0 a b c ∧ ¬ 2 ≤ c) = N (m + 2) pY :=
    N_congr (fun a b c => by simp only [pD0, pY] <;> omega)
  have hev := N_ev (m + 1)
  have hz := N_Z (m + 2)
  have hb1 := (N_B1 (m + 1)).1
  have hb3 := (N_B3 m).1
  have hd := N_D m
  have hy := N_Y (m + 2)
  have hsum : N (m + 2) pSpl + 1 + 2 ^ (m + 1) + (m + 2) * 2 ^ m + (m + 2) * 2 ^ m =
      2 * 4 ^ (m + 1) + (m + 2) := by
    linarith
  have hcast : ((N (m + 2) pSpl : ℕ) : ℤ) + 1 + 2 ^ (m + 1) + (m + 2) * 2 ^ m + (m + 2) * 2 ^ m =
      2 * 4 ^ (m + 1) + (m + 2) := by exact_mod_cast hsum
  have h4 : (4 : ℤ) ^ (m + 1) = 2 ^ (m + 1) * 2 ^ (m + 1) := by
    rw [← mul_pow]; norm_num
  push_cast
  rw [h4] at hcast
  linear_combination 2 * hcast

lemma wit (a b c : ℕ) (h : pSpl a b c) :
    ∃ x y z, x ≤ a ∧ y ≤ b ∧ z ≤ c ∧ 2 * (x + 2 * y + 3 * z) = a + 2 * b + 3 * c := by
  simp only [pSpl] at h
  rcases Nat.mod_two_eq_zero_or_one c with hc | hc <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · exact ⟨a / 2, b / 2, c / 2, by omega, by omega, by omega, by omega⟩
  · by_cases ha : 2 ≤ a
    · exact ⟨a / 2 + 1, (b - 1) / 2, c / 2, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, (b + 3) / 2, c / 2 - 1, by omega, by omega, by omega, by omega⟩
  · by_cases ha : 3 ≤ a
    · exact ⟨(a + 3) / 2, b / 2, (c - 1) / 2, by omega, by omega, by omega, by omega⟩
    · exact ⟨0, b / 2 + 1, (c - 1) / 2, by omega, by omega, by omega, by omega⟩
  · exact ⟨(a + 1) / 2, (b + 1) / 2, (c - 1) / 2, by omega, by omega, by omega, by omega⟩

lemma total_sum {n : ℕ} (S : Finset (Fin n)) (f : Fin n → Fin 4) :
    ∑ i ∈ S, (f i : ℕ) = cS S 1 f + 2 * cS S 2 f + 3 * cS S 3 f := by
  simp only [cS, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  have := (f i).isLt
  split_ifs <;> omega

lemma cS_compl {n : ℕ} (S : Finset (Fin n)) (d : ℕ) (f : Fin n → Fin 4) :
    cS S d f + cS Sᶜ d f = cnt d f := Finset.sum_add_sum_compl S _

lemma ne_zero_iff {n : ℕ} (f : Fin n → Fin 4) : f ≠ 0 ↔ cnt 1 f + cnt 2 f + cnt 3 f ≠ 0 := by
  have h := total_sum Finset.univ f
  simp only [ne_eq, not_iff_not]
  constructor
  · rintro rfl
    simp [cnt, cS]
  · intro h0
    have hs : ∑ i, (f i : ℕ) = 0 := by unfold cnt at h0; omega
    funext i
    rw [Finset.sum_eq_zero_iff] at hs
    exact Fin.ext (by simpa using hs i (Finset.mem_univ _))

lemma crit {n : ℕ} (f : Fin n → Fin 4) :
    (f ≠ 0 ∧ ∃ S : Finset (Fin n), ∑ i ∈ S, (f i : ℕ) = ∑ i ∈ Sᶜ, (f i : ℕ)) ↔
      pSpl (cnt 1 f) (cnt 2 f) (cnt 3 f) := by
  rw [ne_zero_iff]
  constructor
  · rintro ⟨h0, S, hS⟩
    rw [total_sum, total_sum] at hS
    have e1 := cS_compl S 1 f
    have e2 := cS_compl S 2 f
    have e3 := cS_compl S 3 f
    simp only [pSpl]
    omega
  · intro h
    have h0 : cnt 1 f + cnt 2 f + cnt 3 f ≠ 0 := by simp only [pSpl] at h; omega
    refine ⟨h0, ?_⟩
    obtain ⟨x, y, z, hx, hy, hz, he⟩ := wit _ _ _ h
    have hc : ∀ d, cnt d f = (Finset.univ.filter (fun i => (f i : ℕ) = d)).card := by
      intro d
      rw [Finset.card_filter]
      rfl
    obtain ⟨S1, hS1, hc1⟩ := Finset.exists_subset_card_eq (hc 1 ▸ hx)
    obtain ⟨S2, hS2, hc2⟩ := Finset.exists_subset_card_eq (hc 2 ▸ hy)
    obtain ⟨S3, hS3, hc3⟩ := Finset.exists_subset_card_eq (hc 3 ▸ hz)
    have v : ∀ (T : Finset (Fin n)) (d : ℕ),
        T ⊆ Finset.univ.filter (fun i => (f i : ℕ) = d) → ∑ i ∈ T, (f i : ℕ) = d * T.card := by
      intro T d hT
      rw [Finset.sum_congr rfl (fun i hi => (Finset.mem_filter.mp (hT hi)).2), Finset.sum_const,
        smul_eq_mul, mul_comm]
    have dj : ∀ (T U : Finset (Fin n)) (d e : ℕ), d ≠ e →
        T ⊆ Finset.univ.filter (fun i => (f i : ℕ) = d) →
        U ⊆ Finset.univ.filter (fun i => (f i : ℕ) = e) → Disjoint T U := by
      intro T U d e hde hT hU
      rw [Finset.disjoint_left]
      intro i hiT hiU
      exact hde ((Finset.mem_filter.mp (hT hiT)).2.symm.trans (Finset.mem_filter.mp (hU hiU)).2)
    have d12 := dj S1 S2 1 2 (by norm_num) hS1 hS2
    have d123 : Disjoint (S1 ∪ S2) S3 := Finset.disjoint_union_left.mpr
      ⟨dj S1 S3 1 3 (by norm_num) hS1 hS3, dj S2 S3 2 3 (by norm_num) hS2 hS3⟩
    refine ⟨S1 ∪ S2 ∪ S3, ?_⟩
    have hsum : ∑ i ∈ S1 ∪ S2 ∪ S3, (f i : ℕ) = x + 2 * y + 3 * z := by
      rw [Finset.sum_union d123, Finset.sum_union d12, v S1 1 hS1, v S2 2 hS2, v S3 3 hS3,
        hc1, hc2, hc3]
      ring
    have htot := Finset.sum_add_sum_compl (S1 ∪ S2 ∪ S3) (fun i => (f i : ℕ))
    have hT := total_sum Finset.univ f
    simp only [cnt] at he
    omega

lemma a_eq (n : ℕ) : a n = N n pSpl := by
  rw [a, Finset.card_filter, N]
  exact Finset.sum_congr rfl (fun f _ => by rw [if_congr (crit f) rfl rfl])

lemma a_closed (n : ℕ) (hn : 1 ≤ n) : 2 * (a n : ℤ) = (2 ^ n - 2) * (1 + 2 ^ n - n) := by
  rcases Nat.lt_or_ge n 2 with h | h
  · have h1 : n = 1 := by omega
    subst h1
    have h := N_succ 0 pSpl
    simp only [N_zero, pSpl] at h
    have h' : N 1 pSpl = 0 := by simpa using h
    rw [a_eq, h']
    norm_num
  · rw [a_eq]
    exact N_spl n h

end OMA.P_a064671

open OMA.P_a064671 in
theorem OMA.solution : type_of% @OMA.S_oeis_a064671.main := by
  refine ⟨fun n hn => ?_, fun n hn => ?_⟩
  · rw [← a_closed n hn, Int.mul_ediv_cancel_left _ (by norm_num)]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
    rw [show m + 6 - 1 = m + 5 by omega, show m + 6 - 2 = m + 4 by omega,
      show m + 6 - 3 = m + 3 by omega, show m + 6 - 4 = m + 2 by omega,
      show m + 6 - 5 = m + 1 by omega]
    have h6 := a_closed (m + 6) (by omega)
    have h5 := a_closed (m + 5) (by omega)
    have h4 := a_closed (m + 4) (by omega)
    have h3 := a_closed (m + 3) (by omega)
    have h2 := a_closed (m + 2) (by omega)
    have h1 := a_closed (m + 1) (by omega)
    push_cast at h6 h5 h4 h3 h2 h1
    apply mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0)
    linear_combination h6 - 10 * h5 + 37 * h4 - 64 * h3 + 52 * h2 - 16 * h1
