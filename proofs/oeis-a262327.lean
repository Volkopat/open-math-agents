import OMAStatements.S_oeis_a262327

-- Problem: A262327: Number of (n+1) X (3+1) 0..1 arrays with each row and column divisible by 3, read as a binary number with top and left being the most significant bits
-- Upstream: formal-conjectures statements/oeis-a262327.lean:0 (declaration OMA.S_oeis_a262327.main)
-- Credit: @timlantin (the owner of the agent is credited as the solver)
--
-- Proof sketch. Read the rows top to bottom and keep the state s in (ZMod 3)^4 of the column
-- values mod 3 (appending a row x sends s to 2s + x). For f on states put
-- (T f)(s) = sum over the 6 admissible rows x of f(2s + x); then a(n) = (T^(n+1) d)(0) with d the
-- indicator of 0. With IR the indicator of the 6 rows and IV the indicator of the subspace
-- s0 + s2 = s1 + s3, one checks over the 81 states: T d = IR, T IV = 6 IV, T (T IR) = 6 IV + 9 IR.
-- Hence T^(2k+1) d = B_k IV + 9^k IR with 9 B_k + 2 * 9^k = 2 * 36^k, which gives
-- 9 a(2k) = 2 * 36^k + 7 * 9^k and a(2k+1) = 6 a(2k); the closed forms, the recurrence
-- a(n+3) + 54 a(n) = 6 a(n+2) + 9 a(n+1) and the generating series follow.

namespace OMA.P262327
open OMA.S_oeis_a262327

abbrev St := Fin 4 → ZMod 3

def st {m : ℕ} (r : Fin m → Row) : St :=
  fun j => ((binaryValue (fun i => (r i).val j) : ℕ) : ZMod 3)

def bit (x : Fin 4 → Bool) : St := fun j => if x j then 1 else 0

def T (f : St → ℕ) (s : St) : ℕ := ∑ x : Row, f (fun j => 2 * s j + bit x.val j)

def S (m : ℕ) (f : St → ℕ) : ℕ := ∑ r : Fin m → Row, f (st r)

def dl : St → ℕ := fun s => if s = 0 then 1 else 0
def IV : St → ℕ := fun s => if s 0 + s 2 = s 1 + s 3 then 1 else 0
def IR : St → ℕ := fun s =>
  if s 0 ≠ 2 ∧ s 1 ≠ 2 ∧ s 2 ≠ 2 ∧ s 3 ≠ 2 ∧ s 0 + s 2 = s 1 + s 3 then 1 else 0

def Te (f : St → ℕ) (s : St) : ℕ :=
  f (fun j => 2 * s j + ![0,0,0,0] j) + f (fun j => 2 * s j + ![0,0,1,1] j) +
  f (fun j => 2 * s j + ![0,1,1,0] j) + f (fun j => 2 * s j + ![1,0,0,1] j) +
  f (fun j => 2 * s j + ![1,1,0,0] j) + f (fun j => 2 * s j + ![1,1,1,1] j)

lemma S_succ (m : ℕ) (f : St → ℕ) : S (m+1) f = S m (T f) := by
  unfold S T
  rw [← (Fin.snocEquiv (fun _ : Fin (m+1) => Row)).sum_comp, Fintype.sum_prod_type, Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => Finset.sum_congr rfl fun x _ => ?_
  congr 1
  funext j
  simp [st, bit, binaryValue, Fin.snocEquiv]

lemma S_eq (m : ℕ) : ∀ f : St → ℕ, S m f = (T^[m] f) 0 := by
  induction m with
  | zero =>
    intro f
    simp [S]
    rfl
  | succ m ih =>
    intro f
    rw [S_succ, ih, Function.iterate_succ_apply]

lemma a_eq (n : ℕ) : a n = (T^[n+1] dl) 0 := by
  rw [← S_eq]
  unfold a S dl
  rw [Fintype.card_subtype, Finset.card_filter]
  refine Finset.sum_congr rfl fun r _ => ?_
  refine if_congr ?_ rfl rfl
  simp [funext_iff, st, ZMod.natCast_eq_zero_iff]

lemma filt : (Finset.univ.filter (fun r : Fin 4 → Bool => 3 ∣ binaryValue r)) =
    {![false,false,false,false], ![false,false,true,true], ![false,true,true,false],
     ![true,false,false,true], ![true,true,false,false], ![true,true,true,true]} := by
  decide

lemma T_eq (f : St → ℕ) : T f = Te f := by
  funext s
  unfold T Te
  rw [← Finset.sum_subtype (Finset.univ.filter (fun r : Fin 4 → Bool => 3 ∣ binaryValue r))
    (by simp) (fun x => f (fun j => 2 * s j + bit x j)), filt]
  have e1 : bit ![false,false,false,false] = ![0,0,0,0] := by funext j; fin_cases j <;> rfl
  have e2 : bit ![false,false,true,true] = ![0,0,1,1] := by funext j; fin_cases j <;> rfl
  have e3 : bit ![false,true,true,false] = ![0,1,1,0] := by funext j; fin_cases j <;> rfl
  have e4 : bit ![true,false,false,true] = ![1,0,0,1] := by funext j; fin_cases j <;> rfl
  have e5 : bit ![true,true,false,false] = ![1,1,0,0] := by funext j; fin_cases j <;> rfl
  have e6 : bit ![true,true,true,true] = ![1,1,1,1] := by funext j; fin_cases j <;> rfl
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    e1, e2, e3, e4, e5, e6]
  ring

lemma eta (s : St) : s = ![s 0, s 1, s 2, s 3] := by
  funext j; fin_cases j <;> rfl

set_option maxRecDepth 100000 in
lemma d1 : ∀ a b c d : ZMod 3, Te IV ![a,b,c,d] = 6 * IV ![a,b,c,d] := by decide

set_option maxRecDepth 100000 in
lemma d2 : ∀ a b c d : ZMod 3,
    Te (Te IR) ![a,b,c,d] = 6 * IV ![a,b,c,d] + 9 * IR ![a,b,c,d] := by decide

set_option maxRecDepth 100000 in
lemma d3 : ∀ a b c d : ZMod 3, Te dl ![a,b,c,d] = IR ![a,b,c,d] := by decide

lemma TIV : T IV = fun s => 6 * IV s := by
  funext s; rw [T_eq, eta s]; exact d1 _ _ _ _

lemma TTIR : T (T IR) = fun s => 6 * IV s + 9 * IR s := by
  funext s; rw [T_eq, T_eq, eta s]; exact d2 _ _ _ _

lemma Tdl : T dl = IR := by
  funext s; rw [T_eq, eta s]; exact d3 _ _ _ _

lemma T_lin (c d : ℕ) (f g : St → ℕ) :
    T (fun s => c * f s + d * g s) = fun s => c * T f s + d * T g s := by
  funext s
  simp [T, Finset.sum_add_distrib, Finset.mul_sum]

lemma key (k : ℕ) : ∃ B : ℕ, 9 * B + 2 * 9^k = 2 * 36^k ∧
    T^[2*k+1] dl = fun s => B * IV s + 9^k * IR s := by
  induction k with
  | zero => exact ⟨0, by norm_num, by simp [Tdl]⟩
  | succ k ih =>
    obtain ⟨B, hB, h⟩ := ih
    refine ⟨36 * B + 6 * 9^k, by rw [pow_succ, pow_succ]; omega, ?_⟩
    have e : 2 * (k+1) + 1 = 2 + (2*k+1) := by ring
    rw [e, Function.iterate_add_apply, h]
    show T (T _) = _
    have t1 : T (fun s => B * IV s + 9^k * IR s) = fun s => (6*B) * IV s + 9^k * T IR s := by
      rw [T_lin, TIV]; funext s; ring
    rw [t1, T_lin, TIV, TTIR]
    funext s
    ring

lemma vals (k : ℕ) : 9 * a (2*k) = 2 * 36^k + 7 * 9^k ∧ a (2*k+1) = 6 * a (2*k) := by
  obtain ⟨B, hB, h⟩ := key k
  have h0 : a (2*k) = B + 9^k := by
    have i1 : IV 0 = 1 := by decide
    have i2 : IR 0 = 1 := by decide
    rw [a_eq, h]; simp [i1, i2]
  have h1 : a (2*k+1) = 6 * B + 6 * 9^k := by
    rw [a_eq, Function.iterate_succ_apply', h, T_lin, TIV]
    have : T IR 0 = 6 := by rw [T_eq]; decide
    have i1 : IV 0 = 1 := by decide
    simp [this, i1]
    ring
  constructor <;> omega

end OMA.P262327

open OMA.S_oeis_a262327 PowerSeries in
theorem OMA.solution : type_of% @OMA.S_oeis_a262327.main := by
  have V := OMA.P262327.vals
  refine ⟨?_, ?_, ?_⟩
  · intro n hn he
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 * (j+1) := ⟨n / 2 - 1, by omega⟩
    have h := (V (j+1)).1
    have e1 : 3^(2*(j+1)-2) = 9^j := by
      rw [show 2*(j+1)-2 = 2*j by omega, pow_mul]; norm_num
    have e2 : 2^(2*(j+1)+2) = 16 * 4^j := by
      rw [show 2*(j+1)+2 = 2*j+4 by ring, pow_add, pow_mul]; norm_num; ring
    have e3 : (36:ℕ)^j = 9^j * 4^j := by rw [← mul_pow]; norm_num
    rw [e1, e2]
    rw [pow_succ, pow_succ, e3] at h
    nlinarith
  · intro n hn ho
    obtain ⟨k, rfl⟩ : ∃ k, n = 2 * k + 1 := ⟨n / 2, by omega⟩
    have h := V k
    have e1 : 3^(2*k+1-1) = 9^k := by
      rw [show 2*k+1-1 = 2*k by omega, pow_mul]; norm_num
    have e2 : 2^(2*k+1+2) = 8 * 4^k := by
      rw [show 2*k+1+2 = 2*k+3 by ring, pow_add, pow_mul]; norm_num; ring
    have e3 : (36:ℕ)^k = 9^k * 4^k := by rw [← mul_pow]; norm_num
    rw [e1, e2, h.2]
    have h' := h.1
    rw [e3] at h'
    nlinarith
  · have rc : ∀ n, a (n+3) + 54 * a n = 6 * a (n+2) + 9 * a (n+1) := by
      intro n
      rcases Nat.even_or_odd' n with ⟨k, rfl | rfl⟩
      · have h1 := (V (k+1)).2
        have h0 := (V k).2
        rw [show 2*(k+1)+1 = 2*k+3 by ring, show 2*(k+1) = 2*k+2 by ring] at h1
        omega
      · have h2 := (V (k+2)).1
        have h1 := V (k+1)
        have h0 := V k
        rw [show 2*(k+2) = 2*k+1+3 by ring, pow_succ, pow_succ, pow_succ, pow_succ] at h2
        rw [show 2*(k+1)+1 = 2*k+1+2 by ring, show 2*(k+1) = 2*k+1+1 by ring, pow_succ, pow_succ] at h1
        omega
    have a0 : a 0 = 1 := by have := (V 0).1; norm_num at this; omega
    have a1 : a 1 = 6 := by have := (V 0).2; norm_num at this; omega
    have a2 : a 2 = 15 := by have := (V 1).1; norm_num at this; omega
    have a3 : a 3 = 90 := by have := (V 1).2; norm_num at this; omega
    have h9 : (C 9 : PowerSeries ℤ) = C 3 * C 3 := by rw [← map_mul]; norm_num
    have h54 : (C 54 : PowerSeries ℤ) = C 3 * C 3 * C 6 := by rw [← map_mul, ← map_mul]; norm_num
    have h6 : (C 6 : PowerSeries ℤ) = C 3 * C 2 := by rw [← map_mul]; norm_num
    have h21 : (C 21 : PowerSeries ℤ) = C 3 * C 7 := by rw [← map_mul]; norm_num
    have h54' : (C 54 : PowerSeries ℤ) = C 3 * C 18 := by rw [← map_mul]; norm_num
    have hL : (1 - C 3 * X) * (1 + C 3 * X) * (1 - C 6 * X) * generatingSeries =
        generatingSeries - C 6 * (X^1 * generatingSeries) - C 9 * (X^2 * generatingSeries)
          + C 54 * (X^3 * generatingSeries) := by
      rw [h9, h54]; ring
    have hR : (C 3 * X * (C 2 - C 7 * X - C 18 * X^2) : PowerSeries ℤ) =
        C 6 * X^1 - C 21 * X^2 - C 54 * X^3 := by
      rw [h6, h21, h54']; ring
    rw [hL, hR]
    ext n
    simp only [map_add, map_sub, coeff_C_mul, coeff_X_pow_mul', coeff_X_pow, generatingSeries,
      coeff_mk]
    rcases n with _ | _ | _ | _ | m
    · simp
    · simp [a1]
    · simp [a1, a2]
    · simp [a1, a2, a3]
    · have r := rc (m+1)
      have r' : (a (m+1+3) : ℤ) + 54 * a (m+1) = 6 * a (m+1+2) + 9 * a (m+1+1) := by exact_mod_cast r
      simp
      linarith
