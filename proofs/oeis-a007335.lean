import OMAStatements.S_oeis_a007335
import Mathlib

namespace OMA.A007335Proof
open OMA.S_oeis_a007335

def E (p q : ℕ) : Prop :=
  (p = 1 ∧ q = 0) ∨ (p = 0 ∧ q = 1) ∨ (1 ≤ p ∧ q = 1) ∨ (p = 1 ∧ 1 ≤ q) ∨
    (p % 2 = 1 ∧ q % 2 = 1 ∧ 3 ≤ p ∧ 3 ≤ q)

def P (x : ℕ) : Prop := ∃ p q, E p q ∧ x = 2 ^ p * 3 ^ q

lemma fac2 (a b : ℕ) : (2 ^ a * 3 ^ b).factorization 2 = a := by
  rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.prime_two.factorization_self, Nat.prime_three.factorization]

lemma fac3 (a b : ℕ) : (2 ^ a * 3 ^ b).factorization 3 = b := by
  rw [Nat.factorization_mul (by positivity) (by positivity)]
  simp [Nat.prime_two.factorization, Nat.prime_three.factorization_self]

lemma inj {a b c d : ℕ} (h : 2 ^ a * 3 ^ b = 2 ^ c * 3 ^ d) : a = c ∧ b = d := by
  refine ⟨?_, ?_⟩
  · rw [← fac2 a b, h, fac2]
  · rw [← fac3 a b, h, fac3]

lemma coreA1 (a b c d i : ℕ) (h1 : E a b) (h2 : E c d) (hi : a + c = i) (hj : b + d = 1)
    (hi1 : 1 ≤ i) :
    (a = 1 ∧ b = 0 ∧ c = i - 1 ∧ d = 1) ∨ (a = i - 1 ∧ b = 1 ∧ c = 1 ∧ d = 0) := by
  simp only [E] at *; omega

lemma coreA2 (a b c d j : ℕ) (h1 : E a b) (h2 : E c d) (hi : a + c = 1) (hj : b + d = j)
    (hj2 : 2 ≤ j) :
    (a = 0 ∧ b = 1 ∧ c = 1 ∧ d = j - 1) ∨ (a = 1 ∧ b = j - 1 ∧ c = 0 ∧ d = 1) := by
  simp only [E] at *; omega

lemma coreA3 (a b c d i j : ℕ) (h1 : E a b) (h2 : E c d) (hi : a + c = i) (hj : b + d = j)
    (hi3 : 3 ≤ i) (hj3 : 3 ≤ j) (hio : i % 2 = 1) (hjo : j % 2 = 1) :
    (a = i - 1 ∧ b = 1 ∧ c = 1 ∧ d = j - 1) ∨ (a = 1 ∧ b = j - 1 ∧ c = i - 1 ∧ d = 1) := by
  simp only [E] at *; omega

lemma coreB (a b c d : ℕ) (h1 : E a b) (h2 : E c d) (hne : ¬(a = c ∧ b = d))
    (hn : ¬E (a + c) (b + d)) : 2 ≤ a + c ∧ 2 ≤ b + d := by
  simp only [E] at *; omega

lemma minmax {x1 y1 x2 y2 : ℕ} (h1 : min x1 y1 = min x2 y2) (h2 : max x1 y1 = max x2 y2) :
    x1 = x2 ∨ x1 = y2 := by omega


lemma two_le {x : ℕ} (h : P x) : 2 ≤ x := by
  obtain ⟨p, q, hE, rfl⟩ := h
  rcases Nat.eq_zero_or_pos p with hp | hp
  · subst hp
    have hq : 1 ≤ q := by simp only [E] at hE; omega
    have : 3 ≤ 3 ^ q := by
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ q := Nat.pow_le_pow_right (by norm_num) hq
    simpa using this.trans' (by norm_num)
  · have : 2 ≤ 2 ^ p := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) hp
    have : 1 ≤ 3 ^ q := Nat.one_le_pow _ _ (by norm_num)
    nlinarith

lemma up_congr {T S : Set ℕ} {m : ℕ} (hTS : T ⊆ S) (hS : ∀ x ∈ S, x < m → x ∈ T)
    (h2 : ∀ x ∈ S, 2 ≤ x) : UniquePair T m ↔ UniquePair S m := by
  unfold UniquePair
  apply existsUnique_congr
  rintro ⟨x, y⟩
  constructor
  · rintro ⟨hx, hy, hxy, hm⟩
    exact ⟨hTS hx, hTS hy, hxy, hm⟩
  · rintro ⟨hx, hy, hxy, hm⟩
    have h2x := h2 x hx
    have h2y := h2 y hy
    have hym : y < m := by simp only at hm; nlinarith
    exact ⟨hS x hx (by simp only at hxy ⊢; omega), hS y hy hym, hxy, hm⟩

/-- Two distinct splittings contradict uniqueness. -/
lemma twoSplit {m i j : ℕ} (hm : m = 2 ^ i * 3 ^ j) (hU : UniquePair {x | P x} m)
    (a b c d a' b' c' d' : ℕ) (h1 : E a b) (h2 : E c d) (h3 : E a' b') (h4 : E c' d')
    (s1 : a + c = i) (s2 : b + d = j) (s3 : a' + c' = i) (s4 : b' + d' = j)
    (hne : ¬(a = c ∧ b = d)) (hne' : ¬(a' = c' ∧ b' = d'))
    (k1 : ¬(a = a' ∧ b = b')) (k2 : ¬(a = c' ∧ b = d')) : False := by
  have key : ∀ a b c d : ℕ, E a b → E c d → a + c = i → b + d = j → ¬(a = c ∧ b = d) →
      ((min (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d), max (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d)) : ℕ × ℕ).1
        ∈ {x | P x} ∧
      ((min (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d), max (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d)) : ℕ × ℕ).2
        ∈ {x | P x} ∧
      ((min (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d), max (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d)) : ℕ × ℕ).1 <
      ((min (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d), max (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d)) : ℕ × ℕ).2 ∧
      ((min (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d), max (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d)) : ℕ × ℕ).1 *
      ((min (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d), max (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d)) : ℕ × ℕ).2
        = m := by
    intro a b c d ha hc hi hj hn
    have hx : P (2 ^ a * 3 ^ b) := ⟨a, b, ha, rfl⟩
    have hy : P (2 ^ c * 3 ^ d) := ⟨c, d, hc, rfl⟩
    have hxy : 2 ^ a * 3 ^ b ≠ 2 ^ c * 3 ^ d := fun h => hn (inj h)
    have hprod : 2 ^ a * 3 ^ b * (2 ^ c * 3 ^ d) = m := by
      rw [hm, ← hi, ← hj]; ring
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [Set.mem_ofPred_eq]
      rcases le_total (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d) with h | h
      · rw [min_eq_left h]; exact hx
      · rw [min_eq_right h]; exact hy
    · simp only [Set.mem_ofPred_eq]
      rcases le_total (2 ^ a * 3 ^ b) (2 ^ c * 3 ^ d) with h | h
      · rw [max_eq_right h]; exact hy
      · rw [max_eq_left h]; exact hx
    · simp only
      generalize 2 ^ a * 3 ^ b = x at hxy
      generalize 2 ^ c * 3 ^ d = y at hxy
      omega
    · simp only [min_mul_max]; exact hprod
  have e := hU.unique (key a b c d h1 h2 s1 s2 hne) (key a' b' c' d' h3 h4 s3 s4 hne')
  simp only [Prod.mk.injEq] at e
  rcases minmax e.1 e.2 with h | h
  · exact k1 (inj h)
  · exact k2 (inj h)


lemma countB {m : ℕ} (hU : UniquePair {x | P x} m) : P m := by
  obtain ⟨⟨x, y⟩, ⟨hx, hy, hxy, hm⟩, -⟩ := id hU
  obtain ⟨a, b, hab, rfl⟩ := hx
  obtain ⟨c, d, hcd, rfl⟩ := hy
  simp only at hxy hm
  have hm' : m = 2 ^ (a + c) * 3 ^ (b + d) := by rw [← hm]; ring
  by_contra hP
  have hn : ¬E (a + c) (b + d) := fun h => hP ⟨_, _, h, hm'⟩
  have hne : ¬(a = c ∧ b = d) := by
    rintro ⟨rfl, rfl⟩; exact lt_irrefl _ hxy
  obtain ⟨hi, hj⟩ := coreB a b c d hab hcd hne hn
  generalize hI : a + c = i at hm' hn hi
  generalize hJ : b + d = j at hm' hn hj
  have hn' := hn
  simp only [E] at hn'
  rcases (by omega : (i = 2 ∧ j = 2) ∨ (i = 2 ∧ 3 ≤ j) ∨ (3 ≤ i ∧ j = 2) ∨
      (3 ≤ i ∧ 3 ≤ j ∧ i % 2 = 0 ∧ j % 2 = 1) ∨ (3 ≤ i ∧ 3 ≤ j ∧ i % 2 = 1 ∧ j % 2 = 0) ∨
      (3 ≤ i ∧ 3 ≤ j ∧ i % 2 = 0 ∧ j % 2 = 0)) with h | h | h | h | h | h
  · exact twoSplit hm' hU 1 0 1 2 0 1 2 1 (by unfold E; omega) (by unfold E; omega)
      (by unfold E; omega) (by unfold E; omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact twoSplit hm' hU 1 0 1 j 1 1 1 (j - 1) (by unfold E; omega)
      (by unfold E; omega) (by unfold E; omega) (by unfold E; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact twoSplit hm' hU 0 1 i 1 1 1 (i - 1) 1 (by unfold E; omega)
      (by unfold E; omega) (by unfold E; omega) (by unfold E; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact twoSplit hm' hU 1 0 (i - 1) j (i - 1) 1 1 (j - 1) (by unfold E; omega)
      (by unfold E; omega) (by unfold E; omega) (by unfold E; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact twoSplit hm' hU 0 1 i (j - 1) (i - 1) 1 1 (j - 1) (by unfold E; omega)
      (by unfold E; omega) (by unfold E; omega) (by unfold E; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
  · exact twoSplit hm' hU 1 1 (i - 1) (j - 1) (i - 1) 1 1 (j - 1) (by unfold E; omega)
      (by unfold E; omega) (by unfold E; omega) (by unfold E; omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

lemma uniqA {m i j u1 u2 v1 v2 : ℕ} (hm : m = 2 ^ i * 3 ^ j) (hu : E u1 u2) (hv : E v1 v2)
    (hs1 : u1 + v1 = i) (hs2 : u2 + v2 = j) (hne : ¬(u1 = v1 ∧ u2 = v2))
    (hall : ∀ a b c d, E a b → E c d → a + c = i → b + d = j →
      (a = u1 ∧ b = u2 ∧ c = v1 ∧ d = v2) ∨ (a = v1 ∧ b = v2 ∧ c = u1 ∧ d = u2)) :
    UniquePair {x | P x} m := by
  have hX : P (2 ^ u1 * 3 ^ u2) := ⟨u1, u2, hu, rfl⟩
  have hY : P (2 ^ v1 * 3 ^ v2) := ⟨v1, v2, hv, rfl⟩
  have hXY : 2 ^ u1 * 3 ^ u2 ≠ 2 ^ v1 * 3 ^ v2 := fun h => hne (inj h)
  have hprod : 2 ^ u1 * 3 ^ u2 * (2 ^ v1 * 3 ^ v2) = m := by
    rw [hm, ← hs1, ← hs2]; ring
  refine ⟨(min (2 ^ u1 * 3 ^ u2) (2 ^ v1 * 3 ^ v2), max (2 ^ u1 * 3 ^ u2) (2 ^ v1 * 3 ^ v2)),
    ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · simp only [Set.mem_ofPred_eq]
    rcases le_total (2 ^ u1 * 3 ^ u2) (2 ^ v1 * 3 ^ v2) with h | h
    · rw [min_eq_left h]; exact hX
    · rw [min_eq_right h]; exact hY
  · simp only [Set.mem_ofPred_eq]
    rcases le_total (2 ^ u1 * 3 ^ u2) (2 ^ v1 * 3 ^ v2) with h | h
    · rw [max_eq_right h]; exact hY
    · rw [max_eq_left h]; exact hX
  · simp only
    generalize 2 ^ u1 * 3 ^ u2 = x at hXY
    generalize 2 ^ v1 * 3 ^ v2 = y at hXY
    omega
  · simp only [min_mul_max]; exact hprod
  · rintro ⟨x, y⟩ ⟨hx, hy, hxy, hxym⟩
    obtain ⟨a, b, hab, rfl⟩ := hx
    obtain ⟨c, d, hcd, rfl⟩ := hy
    simp only at hxy hxym
    have h2 : 2 ^ (a + c) * 3 ^ (b + d) = 2 ^ i * 3 ^ j := by rw [← hm, ← hxym]; ring
    obtain ⟨e1, e2⟩ := inj h2
    rcases hall a b c d hab hcd e1 e2 with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
    · simp only [Prod.mk.injEq]
      generalize 2 ^ a * 3 ^ b = x at hxy ⊢
      generalize 2 ^ c * 3 ^ d = y at hxy ⊢
      omega
    · simp only [Prod.mk.injEq]
      generalize 2 ^ a * 3 ^ b = x at hxy ⊢
      generalize 2 ^ c * 3 ^ d = y at hxy ⊢
      omega

lemma countA {m : ℕ} (hP : P m) (h3 : 3 < m) : UniquePair {x | P x} m := by
  obtain ⟨i, j, hE, rfl⟩ := hP
  have n10 : ¬(i = 1 ∧ j = 0) := by rintro ⟨rfl, rfl⟩; norm_num at h3
  have n01 : ¬(i = 0 ∧ j = 1) := by rintro ⟨rfl, rfl⟩; norm_num at h3
  have hE' := hE
  simp only [E] at hE'
  by_cases hj : j = 1
  · exact uniqA rfl (u1 := 1) (u2 := 0) (v1 := i - 1) (v2 := 1) (by unfold E; omega)
      (by unfold E; omega) (by omega) (by omega) (by omega)
      (fun a b c d h1 h2 h3 h4 => coreA1 a b c d i h1 h2 h3 (by omega) (by omega))
  by_cases hi : i = 1
  · exact uniqA rfl (u1 := 0) (u2 := 1) (v1 := 1) (v2 := j - 1) (by unfold E; omega)
      (by unfold E; omega) (by omega) (by omega) (by omega)
      (fun a b c d h1 h2 h3 h4 => coreA2 a b c d j h1 h2 (by omega) h4 (by omega))
  · exact uniqA rfl (u1 := i - 1) (u2 := 1) (v1 := 1) (v2 := j - 1) (by unfold E; omega)
      (by unfold E; omega) (by omega) (by omega) (by omega)
      (fun a b c d h1 h2 h3 h4 => coreA3 a b c d i j h1 h2 h3 h4 (by omega) (by omega)
        (by omega) (by omega))


lemma P_inf : (Set.ofPred P).Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro n
  refine ⟨2 ^ (n + 1) * 3 ^ 1, ⟨n + 1, 1, by unfold E; omega, rfl⟩, ?_⟩
  have := Nat.lt_two_pow_self (n := n + 1)
  omega

noncomputable def a : ℕ → ℕ := Nat.nth P

lemma a_mem (n : ℕ) : P (a n) := Nat.nth_mem_of_infinite P_inf n

lemma a_lt {k n : ℕ} : a k < a n ↔ k < n := Nat.nth_lt_nth P_inf

lemma a_range {x : ℕ} (hx : P x) : ∃ k, a k = x := by
  have : x ∈ Set.range (Nat.nth P) := by rw [Nat.range_nth_of_infinite P_inf]; exact hx
  exact this

lemma a0 : a 0 = 2 := by
  have h := Nat.isLeast_nth_of_infinite P_inf 0
  refine h.unique ⟨⟨⟨1, 0, by unfold E; omega, rfl⟩, fun k hk => absurd hk (by omega)⟩, ?_⟩
  rintro x ⟨hx, -⟩
  exact two_le hx

lemma a1 : a 1 = 3 := by
  have h := Nat.isLeast_nth_of_infinite P_inf 1
  refine h.unique ⟨⟨⟨0, 1, by unfold E; omega, rfl⟩, fun k hk => ?_⟩, ?_⟩
  · have : k = 0 := by omega
    subst this
    have := a0
    unfold a at this
    omega
  · rintro x ⟨-, hx⟩
    have := hx 0 (by omega)
    have h0 := a0
    unfold a at h0
    omega

lemma isMU : IsMU a := by
  refine ⟨a0, a1, fun n => ?_⟩
  have hc : ∀ m, m ≤ a (n + 2) →
      (UniquePair (a '' Set.Iic (n + 1)) m ↔ UniquePair {x | P x} m) := by
    intro m hm
    apply up_congr
    · rintro _ ⟨k, -, rfl⟩; exact a_mem k
    · intro x hx hxm
      obtain ⟨k, rfl⟩ := a_range hx
      have : k < n + 2 := a_lt.1 (by omega)
      exact ⟨k, by simp only [Set.mem_Iic]; omega, rfl⟩
    · intro x hx; exact two_le hx
  refine ⟨⟨a_lt.2 (by omega), (hc _ le_rfl).2 (countA (a_mem _) ?_)⟩, ?_⟩
  · rw [← a1]; exact a_lt.2 (by omega)
  · rintro m ⟨hm1, hm2⟩
    by_contra hlt'
    have hlt := not_le.mp hlt'
    have hP := countB ((hc m hlt.le).1 hm2)
    obtain ⟨k, rfl⟩ := a_range hP
    have h1 := a_lt.1 hm1
    have h2 := a_lt.1 hlt
    omega


noncomputable def F (pq : ℕ × ℕ) : ℝ := ((2 : ℝ) ^ pq.1 * 3 ^ pq.2)⁻¹

lemma step1 {s : ℝ} (h : HasSum ({x | P x}.indicator (fun x : ℕ => (x : ℝ)⁻¹)) s) :
    HasSum (fun n => (a n : ℝ)⁻¹) s := by
  have hinj : Function.Injective a := Nat.nth_injective P_inf
  have e : (fun n => (a n : ℝ)⁻¹) = {x | P x}.indicator (fun x : ℕ => (x : ℝ)⁻¹) ∘ a := by
    funext n
    simp only [Function.comp_apply]
    rw [Set.indicator_of_mem (show a n ∈ {x | P x} from a_mem n)]
  rw [e, hinj.hasSum_iff]
  · exact h
  · intro x hx
    apply Set.indicator_of_notMem
    intro hP
    exact hx (a_range hP)

lemma step2 {s : ℝ} (h : HasSum ({pq : ℕ × ℕ | E pq.1 pq.2}.indicator F) s) :
    HasSum ({x | P x}.indicator (fun x : ℕ => (x : ℝ)⁻¹)) s := by
  let g : ℕ × ℕ → ℕ := fun pq => 2 ^ pq.1 * 3 ^ pq.2
  have hinj : Function.Injective g := by
    rintro ⟨p, q⟩ ⟨p', q'⟩ hpq
    obtain ⟨h1, h2⟩ := inj hpq
    exact Prod.ext h1 h2
  have e : {pq : ℕ × ℕ | E pq.1 pq.2}.indicator F =
      {x | P x}.indicator (fun x : ℕ => (x : ℝ)⁻¹) ∘ g := by
    funext ⟨p, q⟩
    simp only [Function.comp_apply, g]
    by_cases hE : E p q
    · rw [Set.indicator_of_mem (show (p, q) ∈ {pq : ℕ × ℕ | E pq.1 pq.2} from hE),
        Set.indicator_of_mem (show 2 ^ p * 3 ^ q ∈ {x | P x} from ⟨p, q, hE, rfl⟩)]
      simp [F]
    · rw [Set.indicator_of_notMem (show (p, q) ∉ {pq : ℕ × ℕ | E pq.1 pq.2} from hE),
        Set.indicator_of_notMem]
      rintro ⟨p', q', hE', h'⟩
      obtain ⟨rfl, rfl⟩ := inj h'
      exact hE hE'
  rw [e, hinj.hasSum_iff] at h
  · exact h
  · intro x hx
    apply Set.indicator_of_notMem
    rintro ⟨p, q, -, rfl⟩
    exact hx ⟨(p, q), rfl⟩


lemma transfer {ι : Type} {A : Set (ℕ × ℕ)} (g : ι → ℕ × ℕ) (hg : Function.Injective g)
    (hmem : ∀ i, g i ∈ A) (hsurj : ∀ x ∈ A, ∃ i, g i = x) {s : ℝ}
    (h : HasSum (fun i => F (g i)) s) : HasSum (A.indicator F) s := by
  have e : (fun i => F (g i)) = A.indicator F ∘ g := by
    funext i
    simp only [Function.comp_apply]
    rw [Set.indicator_of_mem (hmem i)]
  rw [e, hg.hasSum_iff] at h
  · exact h
  · intro x hx
    apply Set.indicator_of_notMem
    intro hA
    obtain ⟨i, rfl⟩ := hsurj x hA
    exact hx ⟨i, rfl⟩

lemma part1 : HasSum (({(1, 0)} : Set (ℕ × ℕ)).indicator F) (1 / 2) := by
  apply transfer (fun _ : Unit => ((1, 0) : ℕ × ℕ))
  · intro i j _; rfl
  · intro i; rfl
  · intro x hx; exact ⟨(), hx.symm⟩
  · have := hasSum_fintype (fun _ : Unit => F (1, 0))
    simp only [Finset.univ_unique, Finset.sum_singleton] at this
    convert this using 1
    norm_num [F]

lemma part2 : HasSum (({(0, 1)} : Set (ℕ × ℕ)).indicator F) (1 / 3) := by
  apply transfer (fun _ : Unit => ((0, 1) : ℕ × ℕ))
  · intro i j _; rfl
  · intro i; rfl
  · intro x hx; exact ⟨(), hx.symm⟩
  · have := hasSum_fintype (fun _ : Unit => F (0, 1))
    simp only [Finset.univ_unique, Finset.sum_singleton] at this
    convert this using 1
    norm_num [F]

lemma part3 : HasSum ({pq : ℕ × ℕ | 1 ≤ pq.1 ∧ pq.2 = 1}.indicator F) (1 / 3) := by
  apply transfer (fun k : ℕ => ((k + 1, 1) : ℕ × ℕ))
  · intro i j h; simp only [Prod.mk.injEq] at h; omega
  · intro i; exact ⟨show 1 ≤ i + 1 by omega, rfl⟩
  · rintro ⟨p, q⟩ ⟨hp, hq⟩
    exact ⟨p - 1, by simp only at hp hq; ext <;> simp only <;> omega⟩
  · have := (hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 6)
    have e1 : (fun k : ℕ => F (k + 1, 1)) = fun k : ℕ => 1 / 6 * (1 / 2 : ℝ) ^ k := by
      funext k
      simp only [F, pow_succ, one_div, inv_pow]
      field_simp
      ring
    have e2 : (1 / 3 : ℝ) = 1 / 6 * (1 - 1 / 2)⁻¹ := by norm_num
    rw [e1, e2]; exact this

lemma part4 : HasSum ({pq : ℕ × ℕ | pq.1 = 1 ∧ 2 ≤ pq.2}.indicator F) (1 / 12) := by
  apply transfer (fun k : ℕ => ((1, k + 2) : ℕ × ℕ))
  · intro i j h; simp only [Prod.mk.injEq] at h; omega
  · intro i; exact ⟨rfl, show 2 ≤ i + 2 by omega⟩
  · rintro ⟨p, q⟩ ⟨hp, hq⟩
    exact ⟨q - 2, by simp only at hp hq; ext <;> simp only <;> omega⟩
  · have := (hasSum_geometric_of_lt_one (r := (1 / 3 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 18)
    have e1 : (fun k : ℕ => F (1, k + 2)) = fun k : ℕ => 1 / 18 * (1 / 3 : ℝ) ^ k := by
      funext k
      simp only [F, pow_succ, one_div, inv_pow]
      field_simp
      ring
    have e2 : (1 / 12 : ℝ) = 1 / 18 * (1 - 1 / 3)⁻¹ := by norm_num
    rw [e1, e2]; exact this

lemma part5 : HasSum ({pq : ℕ × ℕ | pq.1 % 2 = 1 ∧ pq.2 % 2 = 1 ∧ 3 ≤ pq.1 ∧ 3 ≤ pq.2}.indicator F)
    (1 / 144) := by
  apply transfer (fun kl : ℕ × ℕ => ((2 * kl.1 + 3, 2 * kl.2 + 3) : ℕ × ℕ))
  · rintro ⟨i, i'⟩ ⟨j, j'⟩ h; simp only [Prod.mk.injEq] at h ⊢; omega
  · rintro ⟨i, j⟩
    exact ⟨show (2 * i + 3) % 2 = 1 by omega, show (2 * j + 3) % 2 = 1 by omega,
      show 3 ≤ 2 * i + 3 by omega, show 3 ≤ 2 * j + 3 by omega⟩
  · rintro ⟨p, q⟩ ⟨hp, hq, hp3, hq3⟩
    exact ⟨((p - 3) / 2, (q - 3) / 2), by simp only at hp hq hp3 hq3 ⊢; ext <;> simp only <;> omega⟩
  · have hf := (hasSum_geometric_of_lt_one (r := (1 / 4 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 8)
    have hg := (hasSum_geometric_of_lt_one (r := (1 / 9 : ℝ)) (by norm_num) (by norm_num)).mul_left
      (1 / 27)
    have hfn : Summable (fun k : ℕ => ‖(1 / 8 : ℝ) * (1 / 4) ^ k‖) := by
      simp only [Real.norm_eq_abs]; exact hf.summable.abs
    have hgn : Summable (fun k : ℕ => ‖(1 / 27 : ℝ) * (1 / 9) ^ k‖) := by
      simp only [Real.norm_eq_abs]; exact hg.summable.abs
    have := hf.mul hg (summable_mul_of_summable_norm hfn hgn)
    have e1 : (fun kl : ℕ × ℕ => F (2 * kl.1 + 3, 2 * kl.2 + 3)) =
        fun kl : ℕ × ℕ => 1 / 8 * (1 / 4 : ℝ) ^ kl.1 * (1 / 27 * (1 / 9 : ℝ) ^ kl.2) := by
      funext ⟨k, l⟩
      simp only [F, pow_succ, pow_mul, one_div, inv_pow]; norm_num
      field_simp
      ring
    have e2 : (1 / 144 : ℝ) = 1 / 8 * (1 - 1 / 4)⁻¹ * (1 / 27 * (1 - 1 / 9)⁻¹) := by norm_num
    rw [e1, e2]; exact this


lemma partE : HasSum ({pq : ℕ × ℕ | E pq.1 pq.2}.indicator F) (181 / 144) := by
  have h := ((((part1.add part2).add part3).add part4).add part5)
  have e2 : (181 / 144 : ℝ) = 1 / 2 + 1 / 3 + 1 / 3 + 1 / 12 + 1 / 144 := by norm_num
  rw [e2]
  convert h using 1
  funext ⟨p, q⟩
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Set.mem_singleton_iff,
    Prod.mk.injEq]
  split_ifs <;> (try simp only [E] at *) <;> first | (exfalso; omega) | simp

lemma hasSum_a : HasSum (fun n => (a n : ℝ)⁻¹) (181 / 144) := step1 (step2 partE)

end OMA.A007335Proof

theorem OMA.solution : type_of% @OMA.S_oeis_a007335.main := by
  exact ⟨OMA.A007335Proof.a, OMA.A007335Proof.isMU, OMA.A007335Proof.hasSum_a⟩
