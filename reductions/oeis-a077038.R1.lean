import OMAStatements.S_oeis_a077038
import Mathlib

namespace OMA.R_oeis_a077038_R1

open OMA.S_oeis_a077038 Nat Polynomial

private lemma cube_neighbours_not_prime {n : ℕ} (hn : 3 ≤ n) :
    ¬ (n^3-1).Prime ∧ ¬ (n^3+1).Prime := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le hn
  have h₁ : (3+k)^3-1 = (2+k)*(k^2+7*k+13) := by
    have h : 0 < (3+k)^3 := by positivity
    apply (Nat.sub_eq_iff_eq_add h).2
    ring
  have h₂ : (3+k)^3+1 = (4+k)*(k^2+5*k+7) := by ring
  rw [h₁,h₂,Nat.prime_mul_iff,Nat.prime_mul_iff]
  omega

private lemma cube_gap_ge_four {n d : ℕ} (hn : 3 ≤ n) (hd : d ∈ gapsAtCube n) : 4 ≤ d := by
  obtain ⟨p,q,hp,hq,hpc,hcq,rfl⟩ := hd
  obtain ⟨hc₁,hc₂⟩ := cube_neighbours_not_prime hn
  have h₁ : p ≠ n^3-1 := fun he => hc₁ (he ▸ hp)
  have h₂ : q ≠ n^3+1 := fun he => hc₂ (he ▸ hq)
  omega

private lemma cube_least_four_iff {n : ℕ} (hn : 3 ≤ n) :
    IsLeast (gapsAtCube n) 4 ↔ Odd n ∧ (n^3-2).Prime ∧ (n^3+2).Prime := by
  have hc : 27 ≤ n^3 := by simpa using Nat.pow_le_pow_left hn 3
  constructor
  · intro hl
    obtain ⟨p,q,hp,hq,hpc,hcq,he⟩ := hl.1
    obtain ⟨hc₁,hc₂⟩ := cube_neighbours_not_prime hn
    have h₁ : p ≠ n^3-1 := fun he => hc₁ (he ▸ hp)
    have h₂ : q ≠ n^3+1 := fun he => hc₂ (he ▸ hq)
    have hp' : p = n^3-2 := by omega
    have hq' : q = n^3+2 := by omega
    refine ⟨?_, hp' ▸ hp, hq' ▸ hq⟩
    apply Nat.not_even_iff_odd.mp
    intro hn'
    have hv := Nat.even_iff.mp (hn'.pow_of_ne_zero (by decide : 3 ≠ 0))
    have hw := hp.eq_two_or_odd
    omega
  · rintro ⟨_,hp,hq⟩
    exact ⟨⟨n^3-2,n^3+2,hp,hq,by omega,by omega,by omega⟩,
      fun _ hd => cube_gap_ge_four hn hd⟩

private lemma cube077038_gap_of_block {n p d : ℕ}
    (hp : p.Prime) (hq : (p + d).Prime) (hlo : p < n ^ 3) (hhi : n ^ 3 < p + d)
    (hgap : ∀ j : ℕ, 0 < j → j < d → ¬ (p + j).Prime) :
    IsLeast (gapsAtCube n) d := by
  refine ⟨⟨p, p + d, hp, hq, hlo, hhi, by omega⟩, ?_⟩
  rintro e ⟨lo, hi, hloP, hhiP, hloC, hhiC, rfl⟩
  have hL : lo ≤ p := by
    by_contra! h
    have he : p + (lo - p) = lo := by omega
    exact hgap (lo - p) (by omega) (by omega) (he.symm ▸ hloP)
  have hR : p + d ≤ hi := by
    by_contra! h
    have he : p + (hi - p) = hi := by omega
    exact hgap (hi - p) (by omega) (by omega) (he.symm ▸ hhiP)
  omega

private lemma cube077038_fresh (B a j : ℕ) :
    ∃ p s : ℕ, B < p ∧ p.Prime ∧ s^3+j ≡ a [MOD p] := by
  obtain ⟨p, hB, hp, h3⟩ :=
    Nat.forall_exists_prime_gt_and_modEq B (q := 3) (a := 2) (by decide) (by decide)
  let : Fact p.Prime := ⟨hp⟩
  have hmod : p % 3 = 2 := h3
  let x : ZMod p := a - j
  let e := 2*(p/3)+1
  have hpow : (x^e)^3 = x := by
    by_cases hx : x = 0
    · simp [hx, e]
    · have he : e*3 = (p-1)*2+1 := by dsimp [e]; omega
      rw [← pow_mul, he, pow_succ, pow_mul, ZMod.pow_card_sub_one_eq_one hx, one_pow, one_mul]
  refine ⟨p, (x^e).val, hB, hp, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff _ _ _).mp
  push_cast
  rw [ZMod.natCast_zmod_val, hpow]
  exact sub_add_cancel _ _

private lemma cube077038_sieve (a d : ℕ) (S : Finset ℕ) :
    ∃ M r : ℕ, 0 < M ∧
      (∀ p : ℕ, p.Prime → p ∣ M → ∃ j ∈ S, d < p ∧ r^3+j ≡ a [MOD p]) ∧
      (∀ j ∈ S, ∃ p : ℕ, p.Prime ∧ p ∣ M ∧ d < p ∧ r^3+j ≡ a [MOD p]) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨1, 0, by decide, ?_, by simp⟩
    intro p hp h
    exact (hp.not_dvd_one h).elim
  | @insert j S hj ih =>
    obtain ⟨M, r, hM, hprimes, hcover⟩ := ih
    obtain ⟨p, s, hlarge, hp, hs⟩ := cube077038_fresh (M+d) a j
    have hco : M.Coprime p := (hp.coprime_iff_not_dvd.mpr
      (fun h => by have := Nat.le_of_dvd hM h; omega)).symm
    obtain ⟨r', hrM, hrp⟩ := Nat.chineseRemainder hco r s
    have hnew : r'^3+j ≡ a [MOD p] := ((hrp.pow 3).add_right j).trans hs
    have hold (q k : ℕ) (hq : q ∣ M) (hk : r^3+k ≡ a [MOD q]) :
        r'^3+k ≡ a [MOD q] := (((hrM.of_dvd hq).pow 3).add_right k).trans hk
    refine ⟨M*p, r', Nat.mul_pos hM hp.pos, ?_, ?_⟩
    · intro q hq hdiv
      rcases hq.dvd_mul.mp hdiv with h | h
      · obtain ⟨k, hk, hbig, hres⟩ := hprimes q hq h
        exact ⟨k, Finset.mem_insert_of_mem hk, hbig, hold q k h hres⟩
      · have heq := (Nat.prime_dvd_prime_iff_eq hq hp).mp h
        subst q
        exact ⟨j, Finset.mem_insert_self j S, by omega, hnew⟩
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | h
      · exact ⟨p, hp, dvd_mul_left p M, by omega, hnew⟩
      · obtain ⟨q, hq, hdiv, hlarge', hres⟩ := hcover k h
        exact ⟨q, hq, dvd_mul_of_dvd_left hdiv p, hlarge', hold q k hdiv hres⟩

/-- A single progression removes every interior candidate, preserving coprimality
of both endpoint values with its modulus. -/
private lemma cube077038_cover (a d : ℕ) :
    ∃ M r : ℕ, 0 < M ∧ ∀ n : ℕ, M+a+2 ≤ n → n ≡ r [MOD M] →
      (n^3-a).Coprime M ∧ (n^3-a+d).Coprime M ∧
      ∀ j : ℕ, 0 < j → j < d → ¬ (n^3-a+j).Prime := by
  obtain ⟨M, r, hM, hprimes, hcover⟩ := cube077038_sieve a d (Finset.Ioo 0 d)
  refine ⟨M, r, hM, ?_⟩
  intro n hn hcong
  have hn3 : n ≤ n^3 := Nat.le_self_pow (by decide) n
  have hdiv (p j : ℕ) (hpM : p ∣ M) (hres : r^3+j ≡ a [MOD p]) : p ∣ n^3-a+j := by
    have e := ((((hcong.of_dvd hpM).pow 3).add_right j).trans hres).symm.dvd'
    rwa [show n^3+j-a = n^3-a+j by omega] at e
  have hends (k : ℕ) (hk : k = 0 ∨ k = d) : (n^3-a+k).Coprime M := by
    apply Nat.coprime_of_dvd
    intro p hp hpk hpM
    obtain ⟨j, hj, hdp, hres⟩ := hprimes p hp hpM
    obtain ⟨hj₀, hjd⟩ := Finset.mem_Ioo.mp hj
    have hboth := hpk.modEq_zero_nat.trans (hdiv p j hpM hres).modEq_zero_nat.symm
    have heq := (Nat.ModEq.add_left_cancel' (n^3-a) hboth).eq_of_lt_of_lt
      (by omega) (by omega)
    omega
  refine ⟨by simpa using hends 0 (Or.inl rfl), hends d (Or.inr rfl), ?_⟩
  intro j hj₀ hjd hjprime
  obtain ⟨p, hp, hpM, _, hres⟩ := hcover j (Finset.mem_Ioo.mpr ⟨hj₀, hjd⟩)
  have hEq := (Nat.prime_dvd_prime_iff_eq hp hjprime).mp (hdiv p j hpM hres)
  have hle := Nat.le_of_dvd hM hpM
  omega

private lemma cube077038_offsets (d : ℕ) (hd : Even d) (hd₂ : 2 < d) :
    ∃ a b : ℕ, a + b = d ∧ 0 < a ∧ 0 < b ∧
      (¬ ∃ t : ℕ, a = t ^ 3) ∧ (¬ ∃ t : ℕ, b = t ^ 3) ∧ (a = 2 ∨ a = 3) := by
  obtain ⟨m, hm⟩ := hd
  have small {a : ℕ} (ha : 2 ≤ a) (hb : a ≤ 3) : ¬ ∃ t : ℕ, a = t ^ 3 := by
    rintro ⟨t, rfl⟩
    by_cases h : 2 ≤ t
    · have hpow := Nat.pow_le_pow_left h 3
      omega
    · interval_cases t <;> omega
  by_cases h : ∃ k : ℕ, d - 2 = k ^ 3
  · obtain ⟨k, hk⟩ := h
    have hk₂ : 2 ≤ k := by
      by_contra! h
      interval_cases k <;> simp_all <;> omega
    refine ⟨3, d - 3, by omega, by omega, by omega, small (by decide) (by decide), ?_, Or.inr rfl⟩
    rintro ⟨t, ht⟩
    have hlt : t < k := by
      by_contra! htk
      have hpow := Nat.pow_le_pow_left htk 3
      omega
    have hpow : (t + 1)^3 ≤ k^3 := Nat.pow_le_pow_left (Nat.succ_le_of_lt hlt) 3
    by_cases ht₀ : t = 0
    · subst t
      have hkpow := Nat.pow_le_pow_left hk₂ 3
      simp at ht
      omega
    · have ht₁ : 1 ≤ t := by omega
      have hgap : t^3 + 1 < (t+1)^3 := by nlinarith
      omega
  · exact ⟨2, d - 2, by omega, by omega, by omega, small (by decide) (by decide), h, Or.inl rfl⟩

private lemma cube077038_local (a b p : ℕ) (he : Even (a + b)) (hp : p.Prime) :
    ∃ x : ZMod p, x ^ 3 ≠ (a : ZMod p) ∧ x ^ 3 ≠ -(b : ZMod p) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases h₂ : p = 2
  · subst p
    have hsum : (a : ZMod 2) + (b : ZMod 2) = 0 := by
      simpa only [Nat.cast_add] using (ZMod.natCast_eq_zero_iff_even.mpr he)
    have heq : (a : ZMod 2) = -(b : ZMod 2) := eq_neg_of_add_eq_zero_left hsum
    by_cases h : (a : ZMod 2) = 0
    · exact ⟨1, by simp [h], by simp [← heq, h]⟩
    · exact ⟨0, by simpa using Ne.symm h, by simpa [← heq] using Ne.symm h⟩
  · have hm : (-1 : ZMod p) ≠ 1 := by
      intro h
      have heq : ((2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination -h
      have hdiv := (ZMod.natCast_eq_zero_iff 2 p).mp heq
      have hle := Nat.le_of_dvd (by decide : 0 < 2) hdiv
      have := hp.two_le
      omega
    by_contra hn
    have cover (x : ZMod p) : x ^ 3 = (a : ZMod p) ∨ x ^ 3 = -(b : ZMod p) := by
      by_contra! h
      exact hn ⟨x, h⟩
    have h0 := cover 0
    have h1 := cover 1
    have hm1 := cover (-1)
    simp only [zero_pow (by decide : 3 ≠ 0), one_pow,
      show (-1 : ZMod p)^3 = -1 by norm_num] at h0 h1 hm1
    rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases hm1 with h3 | h3 <;> grind

open Polynomial in
private lemma cube077038_affine_irreducible (m k : ℚ) (hm : m ≠ 0) (c : ℤ)
    (hc : ¬ ∃ t : ℕ, c.natAbs = t ^ 3) :
    Irreducible (((C m * X + C k)^3 - C (c : ℚ)) : ℚ[X]) := by
  have mon : (X^3 - C c).Monic := monic_X_pow_sub_C c (by decide)
  have ir : Irreducible (X^3 - C c) := by
    apply (mon.irreducible_iff_roots_eq_zero_of_degree_le_three
      (by rw [natDegree_X_pow_sub_C]; decide) (by rw [natDegree_X_pow_sub_C])).2
    apply Multiset.eq_zero_of_forall_notMem
    intro z hz
    have heq : z^3 = c := by
      simpa [Polynomial.IsRoot, sub_eq_zero] using (mem_roots mon.ne_zero).1 hz
    exact hc ⟨z.natAbs, by rw [← heq, Int.natAbs_pow]⟩
  have irQ : Irreducible ((X^3 - C (c : ℚ)) : ℚ[X]) := by
    simpa using (IsPrimitive.Int.irreducible_iff_irreducible_map_cast mon.isPrimitive).mp ir
  apply irreducible_of_degree_le_three_of_not_isRoot
  · rw [natDegree_sub_C, natDegree_pow, natDegree_add_C, natDegree_C_mul_X _ hm]
    decide
  · intro t ht
    apply (X_pow_sub_C_irreducible_iff_of_prime (by decide : Nat.Prime 3)).mp irQ (m*t+k)
    simpa [Polynomial.IsRoot, sub_eq_zero] using ht

private lemma cube077038_progression (M r a b N : ℕ) (hM : 0 < M) (he : Even (a+b))
    (hcop : ∀ n : ℕ, N ≤ n → n ≡ r [MOD M] → (n^3-a).Coprime M ∧ (n^3+b).Coprime M)
    (p : ℕ) (hp : p.Prime) :
    ∃ k : ℕ, ((r+M*k : ℕ) : ZMod p)^3 ≠ (a : ZMod p) ∧
      ((r+M*k : ℕ) : ZMod p)^3 ≠ -(b : ZMod p) := by
  let : Fact p.Prime := ⟨hp⟩
  by_cases hd : p ∣ M
  · let k := N+a+1
    let n := r+M*k
    have hkn : k ≤ n := (Nat.le_mul_of_pos_left k hM).trans (Nat.le_add_left ..)
    have hN : N ≤ n := by dsimp [k] at hkn; omega
    have ha : a ≤ n^3 := by
      have hpow : n ≤ n^3 := Nat.le_self_pow (by decide) n
      dsimp [k] at hkn
      omega
    have hm : n ≡ r [MOD M] := by simp [n, Nat.ModEq]
    obtain ⟨h₁,h₂⟩ := hcop n hN hm
    have nonzero (z : ℕ) (hc : z.Coprime M) : (z : ZMod p) ≠ 0 := by
      intro hz
      exact Nat.not_coprime_of_dvd_of_dvd hp.one_lt ((ZMod.natCast_eq_zero_iff z p).mp hz) hd hc
    refine ⟨k, ?_, ?_⟩
    · change (n : ZMod p)^3 ≠ a
      have nz := nonzero _ h₁
      rw [Nat.cast_sub ha, Nat.cast_pow, sub_ne_zero] at nz
      exact nz
    · change (n : ZMod p)^3 ≠ -b
      have nz := nonzero _ h₂
      rw [Nat.cast_add, Nat.cast_pow] at nz
      exact fun h => nz (by rw [h, neg_add_cancel])
  · obtain ⟨x,h₁,h₂⟩ := cube077038_local a b p he hp
    have hm : (M : ZMod p) ≠ 0 := fun h => hd ((ZMod.natCast_eq_zero_iff _ _).mp h)
    let t := (x-r) / (M : ZMod p)
    refine ⟨t.val, ?_⟩
    have ht : ((r+M*t.val : ℕ) : ZMod p) = x := by
      push_cast
      rw [ZMod.natCast_zmod_val]
      dsimp [t]
      field_simp
      ring
    simpa only [ht] using And.intro h₁ h₂

/-- The gap of four is the pair of cubic shifts by two. -/
def H1 : Prop :=
  {n : ℕ | Odd n ∧ (n ^ 3 - 2).Prime ∧ (n ^ 3 + 2).Prime}.Infinite

/-- Simultaneous prime values for two admissible irreducible cubics on a progression.
Only lower offsets two and three and even gaps greater than four are needed. -/
def H2 : Prop :=
  ∀ a b M r : ℕ, (a = 2 ∨ a = 3) → 0 < b → Even (a + b) → 4 < a + b → 0 < M →
    let f : ℚ[X] := C (M : ℚ) * X + C (r : ℚ)
    Irreducible (f ^ 3 - C (a : ℚ)) → Irreducible (f ^ 3 + C (b : ℚ)) →
    (∀ p : ℕ, p.Prime → ∃ k : ℕ, ((r + M*k : ℕ) : ZMod p)^3 ≠ (a : ZMod p) ∧
      ((r + M*k : ℕ) : ZMod p)^3 ≠ -(b : ZMod p)) →
    {k : ℕ | ((r + M*k)^3 - a).Prime ∧ ((r + M*k)^3 + b).Prime}.Infinite

theorem main : H1 → H2 → type_of% @OMA.S_oeis_a077038.main := by
  intro hfour hpairs d hd hd₂
  apply Set.infinite_iff_exists_gt.mpr
  intro T
  by_cases heq : d = 4
  · subst d
    obtain ⟨n, hn, hT⟩ := Set.infinite_iff_exists_gt.mp hfour (max T 3)
    exact ⟨n, ⟨by omega, (cube_least_four_iff (by omega)).mpr hn⟩, by omega⟩
  have hd₄ : 4 < d := by obtain ⟨m, hm⟩ := hd; omega
  obtain ⟨a, b, hab, ha, hb, hna, hnb, hshape⟩ := cube077038_offsets d hd hd₂
  obtain ⟨M, r, hM, hcover⟩ := cube077038_cover a d
  have hP := cube077038_affine_irreducible (M : ℚ) (r : ℚ) (by positivity) (a : ℤ)
    (by simpa using hna)
  have hQ := cube077038_affine_irreducible (M : ℚ) (r : ℚ) (by positivity) (-(b : ℤ))
    (by simpa using hnb)
  have hlocal := cube077038_progression M r a b (M+a+2) hM (hab ▸ hd) (by
    intro n hn hmod
    obtain ⟨h₁, h₂, _⟩ := hcover n hn hmod
    have : n ≤ n^3 := Nat.le_self_pow (by decide) n
    exact ⟨h₁, (by simpa only [show n^3-a+d = n^3+b by omega] using h₂)⟩)
  have hinf := hpairs a b M r hshape hb (hab ▸ hd) (by omega) hM hP (by simpa using hQ) hlocal
  obtain ⟨k, ⟨hp, hq⟩, hk⟩ := Set.infinite_iff_exists_gt.mp hinf (max T (M+a+2))
  let n := r + M*k
  have hkn : k ≤ n := (Nat.le_mul_of_pos_left k hM).trans (Nat.le_add_left ..)
  have hn : M+a+2 ≤ n := by omega
  have hn₃ : n ≤ n^3 := Nat.le_self_pow (by decide) n
  have he : n^3 - a + d = n^3 + b := by omega
  obtain ⟨_, _, hgap⟩ := hcover n hn (by simp [n, Nat.ModEq])
  exact ⟨n, ⟨by omega, cube077038_gap_of_block (n := n) (p := n^3-a) (d := d) hp (he.symm ▸ hq)
    (by omega) (by omega) hgap⟩, by omega⟩

end OMA.R_oeis_a077038_R1
