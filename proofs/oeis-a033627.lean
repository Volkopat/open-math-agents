import OMAStatements.S_oeis_a033627
import Mathlib

/-!
Proof of the A033627 conjecture (Ya-Ping Lu): for `n ≥ 1` the number of distinct values of `rho` on `ZMod (10^n)`
is `a(n+1)`.

Plan.
- The greedy sequence is `1, 2, 4`, then `3n - 5` (all numbers `≡ 1 (mod 3)` from `7` on): `A_eq`.
- Orbit framework (any map `g` on a type): if `g^[M+6] = g^[M]` everywhere and no point returns to itself in `1..5`
  steps, then `rho x = T x + 6` with `T x ≤ M` the least `s` such that `g^[s+6] x = g^[s] x`, and if one point has
  `T = M` then the values of `rho` are exactly `6, ..., M + 6`.
- On `ZMod (10^n)`, `n ≥ 2`, with `M = 3n - 3`: the identity `f^[3n+3] = f^[3n-3]` comes from integer valuations
  (`2^n` by the parity contraction, `5^n` by a gain of one factor `5` every three steps through the class `0 mod 5`);
  no return in `1..5` steps is checked modulo `10`; the point `4` has `T = 3n - 3` (an exact valuation chain from
  `f^[5] 4`, for `n ≥ 3`, and a direct check for `n = 2`). The case `n = 1` is a direct check (`M = 1`).
-/

namespace OMA.A033627Proof

open Function OMA.S_oeis_a033627

/-! ### The greedy sequence -/

/-- The closed form of A033627. -/
def c (n : ℕ) : ℕ := if n ≤ 2 then n else 3 * n - 5

theorem c_cases (m : ℕ) : (m ≤ 2 ∧ c m = m) ∨ (3 ≤ m ∧ c m = 3 * m - 5) := by
  unfold c
  split_ifs with h
  · exact Or.inl ⟨h, rfl⟩
  · exact Or.inr ⟨by omega, rfl⟩

theorem sInf_c (n : ℕ) :
    sInf {k : ℕ | c n < k ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → c i + c j ≠ k} = c (n + 1) := by
  have hmem : c (n + 1) ∈ {k : ℕ | c n < k ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → c i + c j ≠ k} := by
    refine ⟨?_, fun i j hi hij hj => ?_⟩
    · rcases c_cases n with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
        rcases c_cases (n + 1) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega
    · rcases c_cases i with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
        rcases c_cases j with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;>
        rcases c_cases (n + 1) with ⟨d1, d2⟩ | ⟨d1, d2⟩ <;> omega
  have hlb : ∀ k ∈ {k : ℕ | c n < k ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → c i + c j ≠ k},
      c (n + 1) ≤ k := by
    rintro k ⟨h1, h2⟩
    have c1 : c 1 = 1 := by decide
    have c2 : c 2 = 2 := by decide
    by_cases hn2 : 2 ≤ n
    · have e1 := h2 1 n le_rfl (by omega) le_rfl
      by_cases hn3 : 3 ≤ n
      · have e2 := h2 2 n (by norm_num) (by omega) le_rfl
        rcases c_cases n with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          rcases c_cases (n + 1) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega
      · rcases c_cases n with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
          rcases c_cases (n + 1) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega
    · rcases c_cases n with ⟨a1, a2⟩ | ⟨a1, a2⟩ <;>
        rcases c_cases (n + 1) with ⟨b1, b2⟩ | ⟨b1, b2⟩ <;> omega
  exact le_antisymm (Nat.sInf_le hmem) (hlb _ (Nat.sInf_mem ⟨_, hmem⟩))

theorem A_eq (n : ℕ) : A033627 n = c n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    cases n with
    | zero => simp [A033627, c]
    | succ n =>
      rw [A033627]
      have hset : {k : ℕ | A033627 n < k ∧
          ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → A033627 i + A033627 j ≠ k} =
          {k : ℕ | c n < k ∧ ∀ i j : ℕ, 1 ≤ i → i < j → j ≤ n → c i + c j ≠ k} := by
        ext k
        simp only [Set.mem_setOf_eq]
        rw [ih n (by omega)]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun i j hi hij hj => ?_⟩
          rw [← ih i (by omega), ← ih j (by omega)]
          exact h2 i j hi hij hj
        · rintro ⟨h1, h2⟩
          refine ⟨h1, fun i j hi hij hj => ?_⟩
          rw [ih i (by omega), ih j (by omega)]
          exact h2 i j hi hij hj
      rw [hset]
      exact sInf_c n

/-! ### The orbit framework -/

theorem iter_eq {β : Type*} (h : β → β) {a b : ℕ} (hab : a = b) (x : β) : h^[a] x = h^[b] x := by
  rw [hab]

theorem it2 {β : Type*} (h : β → β) (m n k : ℕ) (hk : m + n = k) (x : β) :
    h^[m] (h^[n] x) = h^[k] x := by
  rw [← hk, iterate_add_apply]

section Framework

variable {α : Type*} (g : α → α)

theorem periodic_six (M : ℕ) (hup : ∀ x, g^[M + 6] x = g^[M] x) (z : α) (p : ℕ) (hp : 1 ≤ p)
    (hz : g^[p] z = z) : g^[6] z = z := by
  have hq : g^[p * (M + 1)] z = z := by
    rw [iterate_mul]
    exact iterate_fixed hz _
  have hle0 : 1 * (M + 1) ≤ p * (M + 1) := Nat.mul_le_mul hp le_rfl
  have hle : M ≤ p * (M + 1) := by omega
  calc g^[6] z = g^[6] (g^[p * (M + 1)] z) := by rw [hq]
    _ = g^[p * (M + 1) - M] (g^[M + 6] z) := by
        rw [it2 g 6 (p * (M + 1)) (6 + p * (M + 1)) rfl,
          it2 g (p * (M + 1) - M) (M + 6) (6 + p * (M + 1)) (by omega)]
    _ = g^[p * (M + 1) - M] (g^[M] z) := by rw [hup]
    _ = g^[p * (M + 1)] z := it2 g (p * (M + 1) - M) M (p * (M + 1)) (by omega) z
    _ = z := hq

theorem rho_eq (M : ℕ) (hup : ∀ x, g^[M + 6] x = g^[M] x)
    (hlow : ∀ z, ∀ j, 1 ≤ j → j < 6 → g^[j] z ≠ z) (x : α) (s : ℕ)
    (hs : g^[s + 6] x = g^[s] x) (hmin : ∀ s' < s, g^[s' + 6] x ≠ g^[s'] x) :
    sInf {t : ℕ | 1 ≤ t ∧ ∃ s < t, g^[t] x = g^[s] x} = s + 6 := by
  have hmem : s + 6 ∈ {t : ℕ | 1 ≤ t ∧ ∃ s < t, g^[t] x = g^[s] x} :=
    ⟨by omega, s, by omega, hs⟩
  have hlb : ∀ t ∈ {t : ℕ | 1 ≤ t ∧ ∃ s < t, g^[t] x = g^[s] x}, s + 6 ≤ t := by
    rintro t ⟨-, s0, hs0, ht⟩
    have hz : g^[t - s0] (g^[s0] x) = g^[s0] x := by
      rw [it2 g (t - s0) s0 t (by omega)]
      exact ht
    have h6 : 6 ≤ t - s0 := by
      by_contra hc
      exact hlow _ (t - s0) (by omega) (by omega) hz
    have hper := periodic_six g M hup _ (t - s0) (by omega) hz
    have hs0' : s ≤ s0 := by
      by_contra hc
      apply hmin s0 (by omega)
      rw [← it2 g 6 s0 (s0 + 6) (by omega)]
      exact hper
    omega
  exact le_antisymm (Nat.sInf_le hmem) (hlb _ (Nat.sInf_mem ⟨_, hmem⟩))

theorem rho_exists (M : ℕ) (hup : ∀ x, g^[M + 6] x = g^[M] x) (x : α) :
    ∃ s ≤ M, g^[s + 6] x = g^[s] x ∧ ∀ s' < s, g^[s' + 6] x ≠ g^[s'] x := by
  classical
  have hex : ∃ s, g^[s + 6] x = g^[s] x := ⟨M, hup x⟩
  exact ⟨Nat.find hex, Nat.find_min' hex (hup x), Nat.find_spec hex,
    fun s' hs' => Nat.find_min hex hs'⟩

theorem rho_hit (M : ℕ) (hup : ∀ x, g^[M + 6] x = g^[M] x)
    (hlow : ∀ z, ∀ j, 1 ≤ j → j < 6 → g^[j] z ≠ z) (x0 : α)
    (hx0 : M = 0 ∨ g^[M + 5] x0 ≠ g^[M - 1] x0) (j : ℕ) (hj : j ≤ M) :
    sInf {t : ℕ | 1 ≤ t ∧ ∃ s < t, g^[t] (g^[j] x0) = g^[s] (g^[j] x0)} = M - j + 6 := by
  apply rho_eq g M hup hlow
  · rw [it2 g (M - j + 6) j (M + 6) (by omega), it2 g (M - j) j M (by omega)]
    exact hup x0
  · intro s' hs' h
    rcases hx0 with h0 | h0
    · omega
    · apply h0
      rw [it2 g (s' + 6) j (s' + 6 + j) rfl, it2 g s' j (s' + j) rfl] at h
      have h2 := congrArg (g^[M - 1 - (s' + j)]) h
      rw [it2 g (M - 1 - (s' + j)) (s' + 6 + j) (M + 5) (by omega),
        it2 g (M - 1 - (s' + j)) (s' + j) (M - 1) (by omega)] at h2
      exact h2

theorem rho_image [Fintype α] (M : ℕ) (hup : ∀ x, g^[M + 6] x = g^[M] x)
    (hlow : ∀ z, ∀ j, 1 ≤ j → j < 6 → g^[j] z ≠ z) (x0 : α)
    (hx0 : M = 0 ∨ g^[M + 5] x0 ≠ g^[M - 1] x0) :
    (Finset.univ : Finset α).image (fun x => sInf {t : ℕ | 1 ≤ t ∧ ∃ s < t, g^[t] x = g^[s] x}) =
      Finset.Icc 6 (M + 6) := by
  ext r
  simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
  constructor
  · rintro ⟨x, rfl⟩
    obtain ⟨s, hsM, hs, hmin⟩ := rho_exists g M hup x
    rw [rho_eq g M hup hlow x s hs hmin]
    omega
  · rintro ⟨h1, h2⟩
    refine ⟨g^[M + 6 - r] x0, ?_⟩
    rw [rho_hit g M hup hlow x0 hx0 (M + 6 - r) (by omega)]
    omega

end Framework

theorem card_rho (N : ℕ) [NeZero N] (M : ℕ)
    (hup : ∀ x : ZMod N, (sq1 N)^[M + 6] x = (sq1 N)^[M] x)
    (hlow : ∀ z : ZMod N, ∀ j, 1 ≤ j → j < 6 → (sq1 N)^[j] z ≠ z)
    (x0 : ZMod N) (hx0 : M = 0 ∨ (sq1 N)^[M + 5] x0 ≠ (sq1 N)^[M - 1] x0) :
    ((Finset.univ : Finset (ZMod N)).image (rho N)).card = M + 1 := by
  have h : rho N = fun x => sInf {t : ℕ | 1 ≤ t ∧ ∃ s < t, (sq1 N)^[t] x = (sq1 N)^[s] x} := rfl
  rw [h, rho_image (sq1 N) M hup hlow x0 hx0, Nat.card_Icc]
  omega

/-! ### The integer model and residues -/

/-- `F m = m ^ 2 + 1` on the integers. -/
def F (m : ℤ) : ℤ := m ^ 2 + 1

theorem castF (N : ℕ) (a : ℤ) (m : ℕ) : ((F^[m] a : ℤ) : ZMod N) = (sq1 N)^[m] (a : ZMod N) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', ← ih]
    simp [F, sq1]

theorem dvd_of_cast_eq (N : ℕ) (x r : ℤ) (h : (x : ZMod N) = (r : ZMod N)) : (N : ℤ) ∣ x - r :=
  (ZMod.intCast_eq_intCast_iff_dvd_sub r x N).mp h.symm

theorem cast_eq_of_dvd (N : ℕ) (x r : ℤ) (h : (N : ℤ) ∣ x - r) : (x : ZMod N) = (r : ZMod N) :=
  ((ZMod.intCast_eq_intCast_iff_dvd_sub r x N).mpr h).symm

theorem dvd5_of_cast (x : ℤ) (h : (x : ZMod 5) = 0) : (5 : ℤ) ∣ x := by
  have := (ZMod.intCast_zmod_eq_zero_iff_dvd x 5).mp h
  exact_mod_cast this

theorem cast_of_dvd5 (x : ℤ) (h : (5 : ℤ) ∣ x) : (x : ZMod 5) = 0 :=
  (ZMod.intCast_zmod_eq_zero_iff_dvd x 5).mpr (by exact_mod_cast h)

theorem not5_of_cast (x : ℤ) (h : (x : ZMod 5) ≠ 0) : ¬ (5 : ℤ) ∣ x :=
  fun hd => h (cast_of_dvd5 x hd)

theorem F_sub (a b : ℤ) : F b - F a = (b - a) * (b + a) := by
  unfold F
  ring

theorem pres (P a b : ℤ) (h : P ∣ b - a) (m : ℕ) : P ∣ F^[m] b - F^[m] a := by
  induction m with
  | zero => exact h
  | succ m ih =>
    rw [iterate_succ_apply', iterate_succ_apply', F_sub]
    exact dvd_mul_of_dvd_left ih _

theorem pres_le (P a b : ℤ) {m m' : ℕ} (hm : m ≤ m') (h : P ∣ F^[m] b - F^[m] a) :
    P ∣ F^[m'] b - F^[m'] a := by
  rw [← it2 F (m' - m) m m' (by omega) b, ← it2 F (m' - m) m m' (by omega) a]
  exact pres P _ _ h _

/-! ### The factor `2^n` -/

theorem two_adic (a b : ℤ) (h : 2 ∣ b - a) (k : ℕ) : (2 : ℤ) ^ (k + 1) ∣ F^[k] b - F^[k] a := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    rw [iterate_succ_apply', iterate_succ_apply', F_sub, pow_succ]
    apply mul_dvd_mul ih
    have h2 : (2 : ℤ) ∣ F^[k] b - F^[k] a := dvd_trans (dvd_pow_self 2 (Nat.succ_ne_zero k)) ih
    have e : F^[k] b + F^[k] a = (F^[k] b - F^[k] a) + 2 * F^[k] a := by ring
    rw [e]
    exact dvd_add h2 (dvd_mul_right 2 _)

/-! ### The factor `5^n` -/

theorem gain5 (P a b : ℤ) (h : P ∣ b - a) (ha : (5 : ℤ) ∣ a) (hd : (5 : ℤ) ∣ b - a) :
    P * 5 ∣ F b - F a := by
  rw [F_sub]
  apply mul_dvd_mul h
  have e : b + a = (b - a) + 2 * a := by ring
  rw [e]
  exact dvd_add hd (dvd_mul_of_dvd_right ha 2)

theorem five_F3 (y : ℤ) (h : (5 : ℤ) ∣ y) : (5 : ℤ) ∣ F^[3] y := by
  apply dvd5_of_cast
  rw [castF, cast_of_dvd5 y h]
  decide

theorem five_chain (y b : ℤ) (hy : (5 : ℤ) ∣ y) (hd : (5 : ℤ) ∣ b - y) (k : ℕ) :
    (5 : ℤ) ∣ F^[3 * k] y ∧ (5 : ℤ) ^ (k + 1) ∣ F^[3 * k] b - F^[3 * k] y := by
  induction k with
  | zero => exact ⟨hy, by simpa using hd⟩
  | succ k ih =>
    obtain ⟨h1, h2⟩ := ih
    have e : ∀ x, F^[3 * (k + 1)] x = F^[2] (F (F^[3 * k] x)) := fun x => by
      rw [← iterate_succ_apply' F, it2 F 2 (3 * k).succ (3 * (k + 1)) (by omega)]
    refine ⟨?_, ?_⟩
    · rw [e]
      exact five_F3 _ h1
    · rw [e, e, pow_succ]
      apply pres
      exact gain5 _ _ _ h2 h1 (dvd_trans (dvd_pow_self 5 (Nat.succ_ne_zero k)) h2)

theorem five_up (n : ℕ) (hn : 2 ≤ n) (a : ℤ) :
    (5 : ℤ) ^ n ∣ F^[3 * n + 3] a - F^[3 * n - 3] a := by
  obtain ⟨j, hj, hjd⟩ : ∃ j, j ≤ 2 ∧ (5 : ℤ) ∣ F^[j] a := by
    have key : ∀ u : ZMod 5, u = 0 ∨ (sq1 5)^[1] u = 0 ∨ (sq1 5)^[2] u = 0 := by decide
    rcases key (a : ZMod 5) with h | h | h
    · exact ⟨0, by omega, dvd5_of_cast _ h⟩
    · exact ⟨1, by omega, dvd5_of_cast _ (by rw [castF]; exact h)⟩
    · exact ⟨2, by omega, dvd5_of_cast _ (by rw [castF]; exact h)⟩
  have hb : (5 : ℤ) ∣ F^[6] (F^[j] a) - F^[j] a :=
    dvd_sub (five_chain (F^[j] a) (F^[j] a) hjd (by simp) 2).1 hjd
  obtain ⟨h1, h2⟩ := five_chain _ _ hjd hb (n - 2)
  have g1 := gain5 _ _ _ h2 h1 (dvd_trans (dvd_pow_self 5 (Nat.succ_ne_zero _)) h2)
  rw [← pow_succ, show n - 2 + 1 + 1 = n by omega] at g1
  have g2 : (5 : ℤ) ^ n ∣ F^[3 * (n - 2) + 1] (F^[6] (F^[j] a)) - F^[3 * (n - 2) + 1] (F^[j] a) := by
    rw [iterate_succ_apply' F (3 * (n - 2)) (F^[6] (F^[j] a)),
      iterate_succ_apply' F (3 * (n - 2)) (F^[j] a)]
    exact g1
  have g3 := pres_le _ _ _ (show 3 * (n - 2) + 1 ≤ 3 * n - 3 - j by omega) g2
  rw [it2 F 6 j (6 + j) rfl, it2 F (3 * n - 3 - j) (6 + j) (3 * n + 3) (by omega),
    it2 F (3 * n - 3 - j) j (3 * n - 3) (by omega)] at g3
  exact g3

/-! ### `f^[3n+3] = f^[3n-3]` on `ZMod (10^n)`, `n ≥ 2` -/

theorem hup10 (n : ℕ) (hn : 2 ≤ n) (x : ZMod (10 ^ n)) :
    (sq1 (10 ^ n))^[3 * n - 3 + 6] x = (sq1 (10 ^ n))^[3 * n - 3] x := by
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  rw [← castF, ← castF, ZMod.intCast_eq_intCast_iff_dvd_sub,
    show 3 * n - 3 + 6 = 3 * n + 3 by omega]
  have h5 := five_up n hn a
  have h2 : (2 : ℤ) ^ n ∣ F^[3 * n + 3] a - F^[3 * n - 3] a := by
    have hpar : (2 : ℤ) ∣ F^[6] a - a := by
      have key : ∀ u : ZMod 2, (sq1 2)^[6] u = u := by decide
      have h6 := key (a : ZMod 2)
      rw [← castF] at h6
      have := dvd_of_cast_eq 2 _ _ h6
      exact_mod_cast this
    have h7 := two_adic a (F^[6] a) hpar (3 * n - 3)
    rw [it2 F (3 * n - 3) 6 (3 * n + 3) (by omega)] at h7
    exact dvd_trans (pow_dvd_pow 2 (by omega)) h7
  have hc : IsCoprime ((2 : ℤ) ^ n) ((5 : ℤ) ^ n) := by
    have h25 : IsCoprime (2 : ℤ) 5 := ⟨-2, 1, by norm_num⟩
    exact h25.pow
  have e10 : (((10 ^ n : ℕ) : ℤ)) = (2 : ℤ) ^ n * 5 ^ n := by
    push_cast
    rw [← mul_pow]
    norm_num
  rw [e10, dvd_sub_comm]
  exact hc.mul_dvd h2 h5

/-! ### No return in fewer than six steps (checked modulo 10) -/

theorem hlow10 (n : ℕ) (hn : 1 ≤ n) (z : ZMod (10 ^ n)) (j : ℕ) (hj1 : 1 ≤ j) (hj6 : j < 6) :
    (sq1 (10 ^ n))^[j] z ≠ z := by
  intro h
  have hdvd : 10 ∣ 10 ^ n := dvd_pow_self 10 (by omega)
  have hcomm : ∀ (m : ℕ) (w : ZMod (10 ^ n)),
      ZMod.castHom hdvd (ZMod 10) ((sq1 (10 ^ n))^[m] w) =
        (sq1 10)^[m] (ZMod.castHom hdvd (ZMod 10) w) := by
    intro m
    induction m with
    | zero => intro w; rfl
    | succ m ih =>
      intro w
      rw [iterate_succ_apply', iterate_succ_apply', ← ih]
      simp only [sq1, map_add, map_pow, map_one]
  have key : ∀ u : ZMod 10, ∀ j, j < 6 → 1 ≤ j → (sq1 10)^[j] u ≠ u := by decide
  exact key _ j hj6 hj1 (by rw [← hcomm, h])

/-! ### A point with the longest tail -/

theorem unit_step (a b w : ℤ) (e : ℕ) (he : 1 ≤ e) (hab : b - a = 5 ^ e * w)
    (hw : ¬ (5 : ℤ) ∣ w) (ha : ¬ (5 : ℤ) ∣ a) :
    ∃ w' : ℤ, F b - F a = 5 ^ e * w' ∧ ¬ (5 : ℤ) ∣ w' := by
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  refine ⟨w * (b + a), by rw [F_sub, hab]; ring, ?_⟩
  obtain ⟨e', rfl⟩ : ∃ e', e = e' + 1 := ⟨e - 1, by omega⟩
  have hba : b + a = 5 * (5 ^ e' * w) + 2 * a := by linear_combination hab
  have hc : ¬ (5 : ℤ) ∣ b + a := by
    rw [hba]
    generalize 5 ^ e' * w = X
    omega
  exact fun h => (hp5.dvd_mul.mp h).elim hw hc

theorem exact_step (y b w : ℤ) (d : ℕ) (hd : 2 ≤ d) (hy : (25 : ℤ) ∣ y - 5)
    (hb : b - y = 5 ^ d * w) (hw : ¬ (5 : ℤ) ∣ w) :
    (25 : ℤ) ∣ F^[3] y - 5 ∧ ∃ w' : ℤ, F^[3] b - F^[3] y = 5 ^ (d + 1) * w' ∧ ¬ (5 : ℤ) ∣ w' := by
  have hp5 : Prime (5 : ℤ) := Int.prime_iff_natAbs_prime.mpr (by norm_num)
  obtain ⟨s, hs⟩ := id hy
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have hbpy : b + y = 5 * (10 * s + 2 + 5 * (5 ^ e * w)) := by linear_combination hb + 2 * hs
  have c1 : ¬ (5 : ℤ) ∣ 10 * s + 2 + 5 * (5 ^ e * w) := by
    generalize 5 ^ e * w = X
    omega
  have s1 : F b - F y = 5 ^ (e + 2 + 1) * (w * (10 * s + 2 + 5 * (5 ^ e * w))) := by
    rw [F_sub, hb, hbpy]
    ring
  have n1 : ¬ (5 : ℤ) ∣ w * (10 * s + 2 + 5 * (5 ^ e * w)) :=
    fun h => (hp5.dvd_mul.mp h).elim hw c1
  have hy5 : (y : ZMod 5) = 0 := cast_of_dvd5 y ⟨5 * s + 1, by linarith⟩
  have r1 : ¬ (5 : ℤ) ∣ F^[1] y := not5_of_cast _ (by rw [castF, hy5]; decide)
  have r2 : ¬ (5 : ℤ) ∣ F^[2] y := not5_of_cast _ (by rw [castF, hy5]; decide)
  obtain ⟨w2, s2, n2⟩ := unit_step (F y) (F b) _ (e + 2 + 1) (by omega) s1 n1 r1
  obtain ⟨w3, s3, n3⟩ := unit_step (F (F y)) (F (F b)) _ (e + 2 + 1) (by omega) s2 n2 r2
  refine ⟨?_, w3, s3, n3⟩
  have h25 : ((F^[3] y : ℤ) : ZMod 25) = ((5 : ℤ) : ZMod 25) := by
    rw [castF, cast_eq_of_dvd 25 y 5 (by exact_mod_cast hy)]
    decide
  have := dvd_of_cast_eq 25 _ _ h25
  exact_mod_cast this

theorem exact_chain (k : ℕ) : (25 : ℤ) ∣ F^[5 + 3 * k] 4 - 5 ∧
    ∃ w : ℤ, F^[6] (F^[5 + 3 * k] 4) - F^[5 + 3 * k] 4 = 5 ^ (k + 2) * w ∧ ¬ (5 : ℤ) ∣ w := by
  induction k with
  | zero =>
    have b1 : ((F^[5] 4 : ℤ) : ZMod 25) = ((5 : ℤ) : ZMod 25) := by rw [castF]; decide
    have b2 : ((F^[5] 4 : ℤ) : ZMod 125) = ((55 : ℤ) : ZMod 125) := by rw [castF]; decide
    have b3 : ((F^[11] 4 : ℤ) : ZMod 125) = ((80 : ℤ) : ZMod 125) := by rw [castF]; decide
    have d1 : (25 : ℤ) ∣ F^[5] 4 - 5 := by exact_mod_cast dvd_of_cast_eq 25 _ _ b1
    have d2 : (125 : ℤ) ∣ F^[5] 4 - 55 := by exact_mod_cast dvd_of_cast_eq 125 _ _ b2
    have d3 : (125 : ℤ) ∣ F^[11] 4 - 80 := by exact_mod_cast dvd_of_cast_eq 125 _ _ b3
    have e11 : F^[6] (F^[5] 4) = F^[11] 4 := it2 F 6 5 11 rfl 4
    show (25 : ℤ) ∣ F^[5] 4 - 5 ∧
      ∃ w : ℤ, F^[6] (F^[5] 4) - F^[5] 4 = 5 ^ 2 * w ∧ ¬ (5 : ℤ) ∣ w
    rw [e11, show (5 : ℤ) ^ 2 = 25 by norm_num]
    refine ⟨d1, (F^[11] 4 - F^[5] 4) / 25, ?_, ?_⟩
    · omega
    · omega
  | succ k ih =>
    obtain ⟨h1, w, hw, hnd⟩ := ih
    obtain ⟨h2, w', hw', hnd'⟩ := exact_step _ _ w (k + 2) (by omega) h1 hw hnd
    have e : F^[5 + 3 * (k + 1)] 4 = F^[3] (F^[5 + 3 * k] 4) :=
      (it2 F 3 (5 + 3 * k) (5 + 3 * (k + 1)) (by omega) 4).symm
    have ecomm : F^[6] (F^[3] (F^[5 + 3 * k] 4)) = F^[3] (F^[6] (F^[5 + 3 * k] 4)) :=
      (it2 F 6 3 9 rfl _).trans (it2 F 3 6 9 rfl _).symm
    refine ⟨?_, w', ?_, hnd'⟩
    · rw [e]
      exact h2
    · rw [e, ecomm]
      exact hw'.trans (by ring)

theorem wit (n : ℕ) (hn : 3 ≤ n) :
    (sq1 (10 ^ n))^[3 * n - 3 + 5] (4 : ZMod (10 ^ n)) ≠ (sq1 (10 ^ n))^[3 * n - 3 - 1] 4 := by
  intro h
  obtain ⟨-, w, hw, hnd⟩ := exact_chain (n - 3)
  have e1 : F^[6] (F^[5 + 3 * (n - 3)] 4) = F^[3 * n - 3 + 5] 4 :=
    it2 F 6 (5 + 3 * (n - 3)) (3 * n - 3 + 5) (by omega) 4
  have e2 : F^[5 + 3 * (n - 3)] 4 = F^[3 * n - 3 - 1] 4 := iter_eq F (by omega) 4
  rw [e1, e2, show n - 3 + 2 = n - 1 by omega] at hw
  have hcast : ((F^[3 * n - 3 + 5] 4 : ℤ) : ZMod (10 ^ n)) =
      ((F^[3 * n - 3 - 1] 4 : ℤ) : ZMod (10 ^ n)) := by
    rw [castF, castF]
    exact_mod_cast h
  have h10 := dvd_of_cast_eq (10 ^ n) _ _ hcast
  have h5 : (5 : ℤ) ^ n ∣ F^[3 * n - 3 + 5] 4 - F^[3 * n - 3 - 1] 4 := by
    refine dvd_trans ?_ h10
    push_cast
    exact pow_dvd_pow_of_dvd (by norm_num) n
  rw [hw] at h5
  have hpow : (5 : ℤ) ^ n = 5 ^ (n - 1) * 5 := by
    rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ n)]
  rw [hpow] at h5
  exact hnd ((mul_dvd_mul_iff_left (pow_ne_zero _ (by norm_num))).mp h5)

/-! ### Small cases -/

theorem hup1 : ∀ x : ZMod (10 ^ 1), (sq1 (10 ^ 1))^[1 + 6] x = (sq1 (10 ^ 1))^[1] x := by
  decide

theorem wit1 : (sq1 (10 ^ 1))^[1 + 5] (4 : ZMod (10 ^ 1)) ≠ (sq1 (10 ^ 1))^[1 - 1] 4 := by
  decide

theorem wit2 :
    (sq1 (10 ^ 2))^[3 * 2 - 3 + 5] (4 : ZMod (10 ^ 2)) ≠ (sq1 (10 ^ 2))^[3 * 2 - 3 - 1] 4 := by
  decide

end OMA.A033627Proof

open OMA.A033627Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a033627.main := by
  intro n hn
  rw [A_eq]
  rcases (show n = 1 ∨ n = 2 ∨ 3 ≤ n by omega) with rfl | rfl | h3
  · rw [card_rho (10 ^ 1) 1 hup1 (hlow10 1 le_rfl) 4 (Or.inr wit1)]
    decide
  · rw [card_rho (10 ^ 2) (3 * 2 - 3) (hup10 2 le_rfl) (hlow10 2 (by norm_num)) 4 (Or.inr wit2)]
    decide
  · rw [card_rho (10 ^ n) (3 * n - 3) (hup10 n (by omega)) (hlow10 n (by omega)) 4
      (Or.inr (wit n h3))]
    rcases c_cases (n + 1) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
