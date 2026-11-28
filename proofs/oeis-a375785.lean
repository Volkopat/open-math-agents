import OMAStatements.S_oeis_a375785

-- Credit: @qu1r0ra

namespace OMA.CuboidParity

private lemma evenDivisorCount (n : ℕ) (hn : 0 < n) :
    Even (3 * n ^ 2).divisors.card := by
  have hN : 3 * n ^ 2 ≠ 0 := by positivity
  have hp : Nat.Prime 3 := by decide
  have h₃ : 3 ∈ (3 * n ^ 2).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨hp, ⟨n ^ 2, rfl⟩, hN⟩
  have hfactor : (3 * n ^ 2).factorization 3 + 1 = 2 * (n.factorization 3 + 1) := by
    rw [Nat.factorization_mul (by decide) (by positivity), Nat.factorization_pow,
      Finsupp.add_apply, hp.factorization_self, Finsupp.smul_apply, nsmul_eq_mul]
    omega
  rw [Nat.card_divisors hN, even_iff_two_dvd]
  exact (show 2 ∣ (3 * n ^ 2).factorization 3 + 1 by
    rw [hfactor]; exact dvd_mul_right _ _).trans
      (Finset.dvd_prod_of_mem (fun p => (3 * n ^ 2).factorization p + 1) h₃)

private lemma evenOddDivisorCount (n : ℕ) (hn : 0 < n) :
    Even (((3 * n ^ 2).divisors.filter Odd).card) := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    have hN : 3 * n ^ 2 ≠ 0 := by positivity
    by_cases h : Odd n
    · have hprod : Odd (3 * n ^ 2) := (by decide : Odd (3 : ℕ)).mul h.pow
      have hall : (3 * n ^ 2).divisors.filter Odd = (3 * n ^ 2).divisors := by
        exact Finset.filter_eq_self.mpr fun d hd => hprod.of_dvd_nat (Nat.dvd_of_mem_divisors hd)
      rw [hall]
      exact evenDivisorCount n hn
    · have he : n % 2 = 0 := by
        rw [Nat.odd_iff] at h
        omega
      let k := n / 2
      have hnk : n = 2 * k := by dsimp [k]; omega
      have hk : 0 < k := by omega
      have hkn : k < n := by omega
      have hK : 3 * k ^ 2 ≠ 0 := by positivity
      have heq : (3 * n ^ 2).divisors.filter Odd = (3 * k ^ 2).divisors.filter Odd := by
        ext d
        simp only [Finset.mem_filter, Nat.mem_divisors]
        constructor
        · rintro ⟨⟨hd, _⟩, ho⟩
          have hmul : 2 ^ 2 * (3 * k ^ 2) = 3 * n ^ 2 := by rw [hnk]; ring
          exact ⟨⟨(ho.coprime_two_right.pow_right 2).dvd_of_dvd_mul_left
            (hmul.symm ▸ hd), hK⟩, ho⟩
        · rintro ⟨⟨hd, _⟩, ho⟩
          refine ⟨⟨dvd_trans hd ?_, hN⟩, ho⟩
          refine ⟨4, ?_⟩
          rw [hnk]
          ring
      rw [heq]
      exact ih k hkn hk

private def oddFactor (p : ℕ × ℕ) : ℕ := if Odd p.1 then p.1 else p.2

private def orderedFactors (N d : ℕ) : ℕ × ℕ := (min d (N / d), max d (N / d))

theorem oppositeFactorPairs_even (n : ℕ) (hn : 0 < n) :
    Even ((((Finset.Icc 1 (3 * n ^ 2)) ×ˢ (Finset.Icc 1 (3 * n ^ 2))).filter
      fun p : ℕ × ℕ => p.1 ≤ p.2 ∧ p.1 * p.2 = 3 * n ^ 2 ∧ p.1 % 2 ≠ p.2 % 2).card) := by
  classical
  let N := 3 * n ^ 2
  have hN : 0 < N := by dsimp [N]; positivity
  let F := ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)).filter fun p : ℕ × ℕ =>
    p.1 ≤ p.2 ∧ p.1 * p.2 = N ∧ p.1 % 2 ≠ p.2 % 2
  change Even F.card
  have memF {a b : ℕ} : (a,b) ∈ F ↔ 0 < a ∧ 0 < b ∧ a ≤ b ∧ a * b = N ∧ a % 2 ≠ b % 2 := by
    simp only [F, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Prod.fst, Prod.snd]
    constructor
    · rintro ⟨⟨⟨ha, _⟩, ⟨hb, _⟩⟩, hs, heq, hp⟩
      exact ⟨ha, hb, hs, heq, hp⟩
    · rintro ⟨ha, hb, hs, heq, hp⟩
      have haN : a ≤ N := by nlinarith
      have hbN : b ≤ N := by nlinarith
      exact ⟨⟨⟨ha, haN⟩, ⟨hb, hbN⟩⟩, hs, heq, hp⟩
  by_cases he : N % 2 = 0
  · suffices hcard : F.card = (N.divisors.filter Odd).card by
      rw [hcard]
      exact evenOddDivisorCount n hn
    have memD {d : ℕ} : d ∈ N.divisors.filter Odd ↔ d ∣ N ∧ Odd d := by
      simp [Nat.mem_divisors, hN.ne']
    refine Finset.card_bij'
      (fun p _ => oddFactor p) (fun d _ => orderedFactors N d) ?_ ?_ ?_ ?_
    · rintro ⟨a,b⟩ hp
      obtain ⟨_, _, _, hab, hp⟩ := memF.mp hp
      apply memD.mpr
      by_cases ha : Odd a
      · exact ⟨by simpa [oddFactor, ha, ← hab] using dvd_mul_right a b,
          by simpa [oddFactor, ha] using ha⟩
      · have hb : Odd b := by rw [Nat.odd_iff] at ha ⊢; omega
        exact ⟨by simpa [oddFactor, ha, ← hab] using dvd_mul_left b a,
          by simpa [oddFactor, ha] using hb⟩
    · intro d hd
      obtain ⟨hdiv, ho⟩ := memD.mp hd
      have hd0 : 0 < d := ho.pos
      have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdiv
      have hq : 0 < N / d := by
        apply Nat.pos_of_ne_zero
        intro hzero
        exact hN.ne' (by simpa [hzero] using hmul.symm)
      have hqmod : (N / d) % 2 = 0 := by
        have hh := congrArg (fun m : ℕ => m % 2) hmul
        simpa [Nat.mul_mod, Nat.odd_iff.mp ho, he] using hh
      by_cases hle : d ≤ N / d
      · unfold orderedFactors
        rw [min_eq_left hle, max_eq_right hle]
        exact memF.mpr ⟨hd0, hq, hle, hmul, by simp [Nat.odd_iff.mp ho, hqmod]⟩
      · have hle' : N / d ≤ d := by omega
        unfold orderedFactors
        rw [min_eq_right hle', max_eq_left hle']
        exact memF.mpr ⟨hq, hd0, hle', (show (N / d) * d = N from (mul_comm _ _).trans hmul),
          by simp [Nat.odd_iff.mp ho, hqmod]⟩
    · rintro ⟨a,b⟩ hp
      obtain ⟨ha, hb, hs, hab, hp⟩ := memF.mp hp
      by_cases ho : Odd a
      · have hq : N / a = b := Nat.div_eq_of_eq_mul_left ha (by simpa [mul_comm] using hab.symm)
        simp [oddFactor, ho, orderedFactors, hq, min_eq_left hs, max_eq_right hs]
      · have hq : N / b = a := Nat.div_eq_of_eq_mul_left hb (by simpa [mul_comm] using hab.symm)
        simp [oddFactor, ho, orderedFactors, hq, min_eq_right hs, max_eq_left hs]
    · intro d hd
      obtain ⟨hdiv, ho⟩ := memD.mp hd
      have hmul : d * (N / d) = N := Nat.mul_div_cancel' hdiv
      have hqmod : (N / d) % 2 = 0 := by
        have hh := congrArg (fun m : ℕ => m % 2) hmul
        simpa [Nat.mul_mod, Nat.odd_iff.mp ho, he] using hh
      by_cases hle : d ≤ N / d
      · simp [oddFactor, orderedFactors, min_eq_left hle, max_eq_right hle, ho]
      · have hle' : N / d ≤ d := by omega
        simp [oddFactor, orderedFactors, min_eq_right hle', max_eq_left hle',
          Nat.odd_iff, hqmod]
  · have hempty : F = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨a,b⟩ hp
      obtain ⟨_, _, _, hab, hp⟩ := memF.mp hp
      have hmod := congrArg (fun c : ℕ => c % 2) hab
      rw [Nat.mul_mod] at hmod
      have hz : a % 2 = 0 ∨ b % 2 = 0 := by omega
      rcases hz with h | h <;> simp [h] at hmod <;> exact he hmod.symm
    simp [hempty]

end OMA.CuboidParity


namespace OMA.CuboidParity

abbrev Triple := ℕ × ℕ × ℕ

def area (x y z : ℕ) : ℕ := x * y + y * z + x * z

def surface (n x y z : ℕ) : Prop := area x y z = 3 * n ^ 2

def sortedPositive (n : ℕ) (p : Triple) : Prop :=
  0 < p.1 ∧ p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ surface n p.1 p.2.1 p.2.2

def allOdd (p : Triple) : Prop :=
  p.1 % 2 = 1 ∧ p.2.1 % 2 = 1 ∧ p.2.2 % 2 = 1

def mixing (p : Triple) : Prop :=
  ¬ (p.1 % 2 = p.2.1 % 2 ∧ p.2.1 % 2 = p.2.2 % 2)

def oddParent (n : ℕ) (p : Triple) : Prop :=
  p.1 < p.2.1 ∧ allOdd p ∧ surface n p.1 p.2.1 p.2.2

def oddChild (n : ℕ) (p : Triple) : Prop :=
  0 < p.1 ∧ p.2.1 ≤ p.2.2 ∧ p.1 % 2 = 0 ∧
    p.2.1 % 2 = 1 ∧ p.2.2 % 2 = 1 ∧ surface n p.1 p.2.1 p.2.2

def doubleParent (n : ℕ) (p : Triple) : Prop :=
  0 < p.1 ∧ p.1 ≤ p.2.1 ∧ p.1 % 2 ≠ p.2.1 % 2 ∧ surface n p.1 p.2.1 p.2.2

def doubleChild (n : ℕ) (p : Triple) : Prop :=
  0 < p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.1 % 2 = 1 ∧
    p.2.1 % 2 = 0 ∧ p.2.2 % 2 = 0 ∧ surface (2 * n) p.1 p.2.1 p.2.2

private theorem odd_sq_mod_eight (a : ℕ) (ha : a % 2 = 1) : a ^ 2 % 8 = 1 := by
  rw [pow_two, Nat.mul_mod]
  have hb : a % 8 < 8 := Nat.mod_lt _ (by decide)
  have hc : (a % 8) % 2 = 1 := by omega
  generalize a % 8 = b at *
  interval_cases b <;> norm_num at *

private theorem odd_edge_difference {n a b c : ℕ} (hn : n % 2 = 1)
    (ha : a % 2 = 1) (hb : b % 2 = 1) (hc : c % 2 = 1)
    (hab : a ≤ b) (h : surface n a b c) : (b - a) % 4 = 0 := by
  have hs : (a + b) * (a + c) = a ^ 2 + 3 * n ^ 2 := by
    unfold surface area at h
    nlinarith only [h]
  have hsum : (a ^ 2 + 3 * n ^ 2) % 8 = 4 := by
    have hna := odd_sq_mod_eight n hn
    have haa := odd_sq_mod_eight a ha
    omega
  by_contra hdiff
  have hd : (a + b) % 4 = 0 := by omega
  have he : (a + c) % 2 = 0 := by omega
  have hf : (a + b) * (a + c) = 8 * ((a + b) / 4 * ((a + c) / 2)) := by
    have hp : a + b = 4 * ((a + b) / 4) := by omega
    have hq : a + c = 2 * ((a + c) / 2) := by omega
    calc
      (a + b) * (a + c) = (4 * ((a + b) / 4)) * (2 * ((a + c) / 2)) :=
        congrArg₂ (· * ·) hp hq
      _ = _ := by ring
  have hcontra := congrArg (· % 8) (hs.symm.trans hf)
  change (a ^ 2 + 3 * n ^ 2) % 8 = _ at hcontra
  rw [Nat.mul_mod_right] at hcontra
  omega

private theorem odd_pair_diff {n u v w : ℕ} (hn : n % 2 = 1)
    (hu : u % 2 = 0) (hv : v % 2 = 1) (hw : w % 2 = 1) (hle : v ≤ w)
    (h : surface n u v w) : (w - v) % 4 = 2 := by
  have hs : (3 * n ^ 2) % 4 = 3 := by
    have ht := odd_sq_mod_eight n hn
    omega
  have hprod : (u * (v + w)) % 4 = 0 := by
    have hu' : u = 2 * (u / 2) := by omega
    have hvw : v + w = 2 * ((v + w) / 2) := by omega
    have he : u * (v + w) = 4 * (u / 2 * ((v + w) / 2)) := by
      calc
        u * (v + w) = (2 * (u / 2)) * (2 * ((v + w) / 2)) := congrArg₂ (· * ·) hu' hvw
        _ = _ := by ring
    rw [he, Nat.mul_mod_right]
  have hs' : u * (v + w) + v * w = 3 * n ^ 2 := by
    unfold surface area at h
    nlinarith only [h]
  have ht : v * w % 4 = 3 := by omega
  rw [Nat.mul_mod] at ht
  have hv' : v % 4 < 4 := Nat.mod_lt _ (by decide)
  have hw' : w % 4 < 4 := Nat.mod_lt _ (by decide)
  have hv'' : (v % 4) % 2 = 1 := by omega
  have hw'' : (w % 4) % 2 = 1 := by omega
  have hneq : v % 4 ≠ w % 4 := by
    intro he
    rw [← he] at ht
    generalize v % 4 = r at *
    interval_cases r <;> norm_num at *
  omega

private theorem double_pair_diff {n u v w : ℕ}
    (hu : u % 2 = 1) (hv : v % 2 = 0) (hw : w % 2 = 0) (hle : v ≤ w)
    (h : surface (2 * n) u v w) : (w - v) % 4 = 0 := by
  have hs : (v * w) % 4 = 0 := by
    have hv' : v = 2 * (v / 2) := by omega
    have hw' : w = 2 * (w / 2) := by omega
    have he : v * w = 4 * (v / 2 * (w / 2)) := by
      calc
        v * w = (2 * (v / 2)) * (2 * (w / 2)) := congrArg₂ (· * ·) hv' hw'
        _ = _ := by ring
    rw [he, Nat.mul_mod_right]
  have he : u * (v + w) + v * w = 4 * (3 * n ^ 2) := by
    unfold surface area at h
    nlinarith only [h]
  have htemp : u * (v + w) % 4 = 0 := by omega
  by_contra hnd
  have htwo : (v + w) % 4 = 2 := by omega
  rw [Nat.mul_mod, htwo] at htemp
  have hl : u % 4 < 4 := Nat.mod_lt _ (by decide)
  have hr : (u % 4) % 2 = 1 := by omega
  generalize u % 4 = r at *
  interval_cases r <;> norm_num at *

-- For odd n, mark one value of an all-odd triple. The two unmarked edges
-- differ by a positive multiple of four, giving the unique even edge.
def oddEquiv (n : ℕ) (hn : n % 2 = 1) :
    {p : Triple // oddParent n p} ≃ {p : Triple // oddChild n p} where
  toFun := by
    rintro ⟨⟨a,b,c⟩, hab, ⟨ha,hb,hc⟩, hs⟩
    dsimp only at hab ha hb hc hs
    have hmod := odd_edge_difference hn ha hb hc hab.le hs
    have hb' : b = a + 2 * ((b - a) / 2) := by omega
    refine ⟨((b-a)/2,a,a+2*c), ?_⟩
    dsimp only [oddChild]
    refine ⟨by omega, by omega, by omega, ha, by omega, ?_⟩
    generalize (b-a)/2 = u at hb' ⊢
    unfold surface area at hs ⊢
    rw [hb'] at hs
    nlinarith only [hs]
  invFun := by
    rintro ⟨⟨u,v,w⟩, hpos, hle, hu, hv, hw, hs⟩
    dsimp only at hpos hle hu hv hw hs
    have hd := odd_pair_diff hn hu hv hw hle hs
    have hw' : w = v + 2 * ((w - v) / 2) := by omega
    refine ⟨(v,v+2*u,(w-v)/2), ?_⟩
    dsimp only [oddParent, allOdd]
    refine ⟨by omega, ⟨hv, by omega, by omega⟩, ?_⟩
    generalize (w-v)/2 = c at hw' ⊢
    unfold surface area at hs ⊢
    rw [hw'] at hs
    nlinarith only [hs]
  left_inv := by
    rintro ⟨⟨a,b,c⟩, hab, ⟨ha,hb,hc⟩, hs⟩
    dsimp only at hab ha hb hc
    apply Subtype.ext
    change (a, a + 2 * ((b-a)/2), (a+2*c-a)/2) = (a,b,c)
    have h1 : a + 2 * ((b-a)/2) = b := by omega
    have h2 : (a+2*c-a)/2 = c := by omega
    rw [h1,h2]
  right_inv := by
    rintro ⟨⟨u,v,w⟩, hpos, hle, hu, hv, hw, hs⟩
    dsimp only at hle hv hw
    apply Subtype.ext
    change ((v+2*u-v)/2, v, v+2*((w-v)/2)) = (u,v,w)
    have h1 : (v+2*u-v)/2 = u := by omega
    have h2 : v+2*((w-v)/2) = w := by omega
    rw [h1,h2]

-- For doubling, the unmarked edges have opposite parities. Their difference
-- is the unique odd edge of the larger triple.
def doubleEquiv (n : ℕ) :
    {p : Triple // doubleParent n p} ≃ {p : Triple // doubleChild n p} where
  toFun := by
    rintro ⟨⟨a,b,c⟩, ha, hab, hmod, hs⟩
    dsimp only at ha hab hmod hs
    refine ⟨(b-a,2*a,2*a+4*c), ?_⟩
    dsimp only [doubleChild]
    refine ⟨by omega, by omega, by omega, by omega, by omega, ?_⟩
    unfold surface area at hs ⊢
    have hb : b = a + (b - a) := by omega
    generalize b - a = u at hb ⊢
    rw [hb] at hs
    nlinarith only [hs]
  invFun := by
    rintro ⟨⟨u,v,w⟩, hvpos, hle, hu, hv, hw, hs⟩
    dsimp only at hvpos hle hu hv hw hs
    have hd := double_pair_diff hu hv hw hle hs
    have he : w = v + 4 * ((w - v) / 4) := by omega
    have hv' : v = 2 * (v / 2) := by omega
    refine ⟨(v/2,v/2+u,(w-v)/4), ?_⟩
    dsimp only [doubleParent]
    refine ⟨by omega, by omega, by omega, ?_⟩
    unfold surface area at hs ⊢
    generalize v / 2 = a at hv' ⊢
    generalize (w-v)/4 = c at he ⊢
    rw [he,hv'] at hs
    nlinarith only [hs]
  left_inv := by
    rintro ⟨⟨a,b,c⟩, ha, hab, hmod, hs⟩
    dsimp only at hab
    apply Subtype.ext
    change (2*a/2, 2*a/2+(b-a), (2*a+4*c-2*a)/4) = (a,b,c)
    simp only [Prod.mk.injEq]
    omega
  right_inv := by
    rintro ⟨⟨u,v,w⟩, hvpos, hle, hu, hv, hw, hs⟩
    dsimp only at hvpos hle hu hv hw hs
    have hd := double_pair_diff hu hv hw hle hs
    apply Subtype.ext
    change (v/2+u-v/2, 2*(v/2), 2*(v/2)+4*((w-v)/4)) = (u,v,w)
    simp only [Prod.mk.injEq]
    omega

end OMA.CuboidParity
namespace OMA.CuboidParity

open Finset

def sortedNonnegative (n : ℕ) (p : Triple) : Prop :=
  p.1 ≤ p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ surface n p.1 p.2.1 p.2.2

noncomputable def cells (n : ℕ) (P : Triple → Prop) : Finset Triple := by
  classical
  let side := Finset.Icc 0 (3 * n ^ 2)
  exact (side ×ˢ side ×ˢ side).filter P

private theorem area_bounds {n x y z : ℕ} (hn : 0 < n)
    (h : surface n x y z) : x ≤ 3 * n ^ 2 ∧ y ≤ 3 * n ^ 2 ∧ z ≤ 3 * n ^ 2 := by
  unfold surface area at h
  have hpos : 0 < 3 * n ^ 2 := by positivity
  have aux {a b c : ℕ} (hs : a*b+b*c+a*c = 3*n^2) : a ≤ 3*n^2 := by
    by_cases hb : 0 < b
    · have hle := Nat.le_mul_of_pos_right a hb
      omega
    · by_cases hc : 0 < c
      · have hle := Nat.le_mul_of_pos_right a hc
        omega
      · have hb' : b = 0 := by omega
        have hc' : c = 0 := by omega
        simp [hb', hc'] at hs
        omega
  exact ⟨aux h, aux (a := y) (b := x) (c := z) (by nlinarith only [h]),
    aux (a := z) (b := x) (c := y) (by nlinarith only [h])⟩

theorem mem_cells {P : Triple → Prop} {n : ℕ} (hn : 0 < n)
    (hs : ∀ p : Triple, P p → surface n p.1 p.2.1 p.2.2) (p : Triple) :
    p ∈ cells n P ↔ P p := by
  classical
  rcases p with ⟨a,b,c⟩
  simp only [cells, Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, zero_le, true_and]
  exact ⟨And.right, fun h => ⟨area_bounds hn (hs (a,b,c) h), h⟩⟩

theorem card_cells_equiv {P Q : Triple → Prop} {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (hP : ∀ p : Triple, P p → surface n p.1 p.2.1 p.2.2)
    (hQ : ∀ p : Triple, Q p → surface m p.1 p.2.1 p.2.2)
    (e : {p // P p} ≃ {p // Q p}) : (cells n P).card = (cells m Q).card := by
  refine Finset.card_bij'
    (fun p hp => (e ⟨p, (mem_cells hn hP p).mp hp⟩).val)
    (fun q hq => (e.symm ⟨q, (mem_cells hm hQ q).mp hq⟩).val)
    (fun q hq => (mem_cells hm hQ _).mpr (e _).property)
    (fun p hp => (mem_cells hn hP _).mpr (e.symm _).property) ?_ ?_
  · intro p hp
    exact congrArg Subtype.val (e.symm_apply_apply ⟨p, (mem_cells hn hP p).mp hp⟩)
  · intro q hq
    exact congrArg Subtype.val (e.apply_symm_apply ⟨q, (mem_cells hm hQ q).mp hq⟩)

-- Insert a marked edge into two ordered edges. Picking the same distinct value
-- recovers the ordered unmarked pair, including when some edges coincide.
def put (a b c : ℕ) : Triple :=
  if c ≤ a then (c,a,b) else if c ≤ b then (a,c,b) else (a,b,c)

def pick (p : Triple) (c : ℕ) : Triple :=
  if c = p.1 then (p.2.1,p.2.2,c)
  else if c = p.2.1 then (p.1,p.2.2,c)
  else (p.1,p.2.1,c)

def edges (p : Triple) : Finset ℕ := {p.1, p.2.1, p.2.2}

theorem put_sorted {a b c : ℕ} (h : a ≤ b) :
    (put a b c).1 ≤ (put a b c).2.1 ∧ (put a b c).2.1 ≤ (put a b c).2.2 := by
  by_cases hca : c ≤ a <;> by_cases hcb : c ≤ b <;> simp [put,hca,hcb] <;> omega

theorem area_put (a b c : ℕ) :
    area (put a b c).1 (put a b c).2.1 (put a b c).2.2 = area a b c := by
  by_cases hca : c ≤ a <;> by_cases hcb : c ≤ b <;> simp [put,hca,hcb,area] <;> ring

theorem put_mem_edges (a b c : ℕ) : c ∈ edges (put a b c) := by
  by_cases hca : c ≤ a <;> by_cases hcb : c ≤ b <;> simp [put,hca,hcb,edges]

theorem pick_put {a b c : ℕ} (h : a ≤ b) : pick (put a b c) c = (a,b,c) := by
  by_cases hca : c ≤ a
  · simp [put,pick,hca]
  · have hne : c ≠ a := by omega
    by_cases hcb : c ≤ b
    · simp [put,pick,hca,hcb,hne]
    · have hne' : c ≠ b := by omega
      simp [put,pick,hca,hcb,hne,hne']

theorem put_pick {x y z c : ℕ} (hxy : x ≤ y) (hyz : y ≤ z)
    (hm : c ∈ edges (x,y,z)) :
    put (pick (x,y,z) c).1 (pick (x,y,z) c).2.1 c = (x,y,z) := by
  simp only [edges, Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with h | h | h <;> subst c
  · simp [pick, put, hxy]
  · by_cases he : y = x
    · subst y
      simp [pick, put, hyz]
    · simp [pick, put, he, show ¬ y ≤ x by omega, hyz]
  · by_cases he : z = x
    · have he' : y = x := by omega
      subst z
      subst y
      simp [pick, put]
    · by_cases he' : z = y
      · subst z
        simp [pick, put, he, show ¬ y ≤ x by omega]
      · simp [pick, put, he, he', show ¬ z ≤ x by omega, show ¬ z ≤ y by omega]

theorem pick_order {x y z : ℕ} (hxy : x ≤ y) (hyz : y ≤ z) (c : ℕ) :
    (pick (x,y,z) c).1 ≤ (pick (x,y,z) c).2.1 := by
  simp only [pick, Prod.fst, Prod.snd]
  split_ifs <;> dsimp only <;> omega

theorem area_pick {x y z c : ℕ} (hm : c ∈ edges (x,y,z)) :
    area (pick (x,y,z) c).1 (pick (x,y,z) c).2.1 c = area x y z := by
  by_cases hcx : c = x
  · subst c
    simp [pick,area]
    ring
  · by_cases hcy : c = y
    · subst c
      simp [pick,area,hcx]
      ring
    · have hcz : c = z := by simpa [edges,hcx,hcy] using hm
      subst c
      simp [pick,hcx,hcy]


end OMA.CuboidParity
namespace OMA.CuboidParity

open Finset
open scoped BigOperators

noncomputable def marked (n : ℕ) (S P : Triple → Prop) :
    Finset (Sigma (fun _ : Triple => ℕ)) := by
  classical
  exact (cells n S).sigma fun p => (edges p).filter fun c => P (pick p c)

theorem pick_mark (p : Triple) (c : ℕ) : (pick p c).2.2 = c := by
  unfold pick
  split_ifs <;> rfl

theorem card_marked {n : ℕ} {S P : Triple → Prop} (hn : 0 < n)
    (hS : ∀ p, S p → sortedNonnegative n p)
    (hord : ∀ p, P p → p.1 ≤ p.2.1)
    (hP : ∀ p, P p → S (put p.1 p.2.1 p.2.2)) :
    (cells n P).card = (marked n S P).card := by
  classical
  have hsurface : ∀ p : Triple, P p → surface n p.1 p.2.1 p.2.2 := by
    intro p hp
    have hh := (hS _ (hP _ hp)).2.2
    unfold surface at *
    rwa [area_put] at hh
  have hsurfaceS : ∀ p, S p → surface n p.1 p.2.1 p.2.2 := fun p hp => (hS p hp).2.2
  refine Finset.card_nbij'
    (fun p => ⟨put p.1 p.2.1 p.2.2,p.2.2⟩)
    (fun q => pick q.1 q.2) ?_ ?_ ?_ ?_
  · intro p hp
    have hp' := (mem_cells hn hsurface _).mp hp
    simpa [marked, mem_sigma, mem_filter, mem_cells hn hsurfaceS, put_mem_edges,
      pick_put (hord _ hp'), hP _ hp', hp']
  · rintro ⟨p,c⟩ hp
    simpa [marked, mem_sigma, mem_filter, mem_cells hn hsurface] using
      ((Finset.mem_filter.mp (Finset.mem_sigma.mp hp).2).2 : P (pick p c))
  · intro p hp
    exact pick_put (hord _ ((mem_cells hn hsurface _).mp hp))
  · rintro ⟨⟨x,y,z⟩,c⟩ hp
    have hh := Finset.mem_sigma.mp hp
    have hsort := hS _ ((mem_cells hn hsurfaceS _).mp hh.1)
    obtain ⟨hxy, hyz, _⟩ := hsort
    have hc := (Finset.mem_filter.mp hh.2).1
    simp only [pick_mark, put_pick hxy hyz hc]

theorem area_rem (m x y z : ℕ) :
    area x y z ≡ area (x % m) (y % m) (z % m) [MOD m] := by
  have hx := (Nat.mod_modEq x m).symm
  have hy := (Nat.mod_modEq y m).symm
  have hz := (Nat.mod_modEq z m).symm
  exact ((hx.mul hy).add (hy.mul hz)).add (hx.mul hz)

theorem surface_rem {m n x y z : ℕ} (h : surface n x y z) :
    area (x % m) (y % m) (z % m) ≡ 3 * (n % m) ^ 2 [MOD m] := by
  have hl := (area_rem m x y z).symm
  rw [show area x y z = 3 * n ^ 2 from h] at hl
  exact hl.trans (((Nat.mod_modEq n m).symm.pow 2).mul_left 3)

def special (n r : ℕ) (p : Triple) : Prop :=
  0 < p.1 ∧ 0 < p.2.1 ∧ p.2.1 ≤ p.2.2 ∧ p.1 % 2 = r ∧
    p.2.1 % 2 ≠ r ∧ p.2.2 % 2 ≠ r ∧ surface n p.1 p.2.1 p.2.2

def chosen (p : Triple) (r : ℕ) : ℕ :=
  if p.1 % 2 = r then p.1 else if p.2.1 % 2 = r then p.2.1 else p.2.2

theorem chosen_put {u v w r : ℕ} (hu : u % 2 = r) (hv : v % 2 ≠ r) (hw : w % 2 ≠ r) :
    chosen (put v w u) r = u := by
  by_cases h1 : u ≤ v <;> by_cases h2 : u ≤ w <;> simp [put, h1, h2, chosen, hu, hv, hw]

theorem chosen_mem (p : Triple) (r : ℕ) : chosen p r ∈ edges p := by
  by_cases h1 : p.1 % 2 = r <;> by_cases h2 : p.2.1 % 2 = r <;> simp [chosen, h1, h2, edges]

theorem special_put {n r : ℕ} {p : Triple} (hp : special n r p) :
    sortedPositive n (put p.2.1 p.2.2 p.1) ∧ mixing (put p.2.1 p.2.2 p.1) := by
  rcases p with ⟨u,v,w⟩
  obtain ⟨hu,hv,hvw,hru,hrv,hrw,hs⟩ := hp
  dsimp only at hu hv hvw hru hrv hrw hs
  refine ⟨⟨?_, (put_sorted hvw).1, (put_sorted hvw).2, ?_⟩, ?_⟩
  · unfold put
    split <;> (first | split | skip) <;> dsimp <;> omega
  · unfold surface at *
    rwa [area_put, show area v w u = area u v w by unfold area; ring]
  · unfold put
    split <;> (first | split | skip) <;> simp [mixing] <;> omega

theorem special_pick {n r : ℕ} {p : Triple} (hsp : sortedPositive n p)
    (hex : (p.1 % 2 = r ∧ p.2.1 % 2 ≠ r ∧ p.2.2 % 2 ≠ r) ∨
      (p.1 % 2 ≠ r ∧ p.2.1 % 2 = r ∧ p.2.2 % 2 ≠ r) ∨
      (p.1 % 2 ≠ r ∧ p.2.1 % 2 ≠ r ∧ p.2.2 % 2 = r)) :
    special n r (chosen p r,(pick p (chosen p r)).1,(pick p (chosen p r)).2.1) := by
  rcases p with ⟨x,y,z⟩
  obtain ⟨hx,hxy,hyz,hs⟩ := hsp
  dsimp only at hx hxy hyz hs hex
  rcases hex with ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩ | ⟨h1,h2,h3⟩
  · simpa [chosen, pick, h1] using
      (show special n r (x,y,z) from ⟨hx, show 0 < y by omega, hyz, h1, h2, h3, hs⟩)
  · have hne : y ≠ x := by rintro rfl; contradiction
    have hs' : surface n y x z := by unfold surface area at *; nlinarith only [hs]
    simpa [chosen, pick, h1, h2, hne] using
      (show special n r (y,x,z) from ⟨show 0 < y by omega, hx, show x ≤ z by omega, h2, h1, h3, hs'⟩)
  · have hne : z ≠ x := by rintro rfl; contradiction
    have hne' : z ≠ y := by rintro rfl; contradiction
    have hs' : surface n z x y := by unfold surface area at *; nlinarith only [hs]
    simpa [chosen, pick, h1, h2, hne, hne'] using
      (show special n r (z,x,y) from ⟨show 0 < z by omega, hx, hxy, h3, h1, h2, hs'⟩)

end OMA.CuboidParity
namespace OMA.CuboidParity

open Finset
open scoped BigOperators

def positiveOdd (n : ℕ) (p : Triple) : Prop := sortedPositive n p ∧ allOdd p

def positiveMixed (n : ℕ) (p : Triple) : Prop := sortedPositive n p ∧ mixing p

def positiveEven (n : ℕ) (p : Triple) : Prop :=
  sortedPositive n p ∧ p.1 % 2 = 0 ∧ p.2.1 % 2 = 0 ∧ p.2.2 % 2 = 0

def exception (n : ℕ) (p : Triple) : Prop :=
  sortedNonnegative n p ∧
    ((p.1 = 0 ∧ p.2.1 % 2 ≠ p.2.2 % 2) ∨
      (0 < p.1 ∧ mixing p ∧ (p.1 = p.2.1 ∨ p.2.1 = p.2.2)))

theorem cells_and (n : ℕ) (P Q : Triple → Prop) [DecidablePred Q] :
    cells n (fun p => P p ∧ Q p) = (cells n P).filter Q := by
  classical
  ext p
  simp only [cells, mem_filter]
  tauto

theorem parity_cases {n x y z : ℕ} (h : surface n x y z) (r : ℕ)
    (hr : r ≤ 1) (hn : n % 2 = 1 - r) :
    ((x % 2 = 1-r ∧ y % 2 = 1-r ∧ z % 2 = 1-r) ↔ ¬ mixing (x,y,z)) ∧
    (mixing (x,y,z) →
      (x % 2 = r ∧ y % 2 ≠ r ∧ z % 2 ≠ r) ∨
      (x % 2 ≠ r ∧ y % 2 = r ∧ z % 2 ≠ r) ∨
      (x % 2 ≠ r ∧ y % 2 ≠ r ∧ z % 2 = r)) := by
  have hrem := @surface_rem 2 n x y z h
  rcases (show r = 0 ∨ r = 1 by omega) with rfl | rfl <;>
    rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with hx | hx <;>
    rcases (show y % 2 = 0 ∨ y % 2 = 1 by omega) with hy | hy <;>
    rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with hz | hz <;>
    rw [hx, hy, hz, hn] at hrem <;>
    norm_num [area, Nat.ModEq] at hrem <;>
    simp [hx, hy, hz, mixing]

def specialEquiv (n r : ℕ) (hr : r ≤ 1) (hn : n % 2 = 1-r) :
    {p : Triple // special n r p} ≃ {p : Triple // positiveMixed n p} where
  toFun p := ⟨put p.val.2.1 p.val.2.2 p.val.1, special_put p.property⟩
  invFun p := ⟨(chosen p.val r,(pick p.val (chosen p.val r)).1,
      (pick p.val (chosen p.val r)).2.1),
    special_pick p.property.1 ((parity_cases p.property.1.2.2.2 r hr hn).2 p.property.2)⟩
  left_inv := by
    rintro ⟨⟨u,v,w⟩,hu,hv,hle,h1,h2,h3,hs⟩
    dsimp only at hle h1 h2 h3
    apply Subtype.ext
    change (chosen (put v w u) r, (pick (put v w u) (chosen (put v w u) r)).1,
      (pick (put v w u) (chosen (put v w u) r)).2.1) = (u,v,w)
    rw [chosen_put h1 h2 h3, pick_put hle]
  right_inv := by
    rintro ⟨⟨x,y,z⟩,hs,hm⟩
    apply Subtype.ext
    exact put_pick hs.2.1 hs.2.2.1 (chosen_mem (x,y,z) r)

theorem card_odd_child (n : ℕ) (hn : n % 2 = 1) :
    (cells n (oddChild n)).card = (cells n (positiveMixed n)).card := by
  have hp : 0 < n := by omega
  have he : oddChild n = special n 0 := by
    funext p
    apply propext
    unfold oddChild special
    constructor
    · rintro ⟨hu,hle,hru,hrv,hrw,hs⟩
      exact ⟨hu,by omega,hle,hru,by omega,by omega,hs⟩
    · rintro ⟨hu,hv,hle,hru,hrv,hrw,hs⟩
      exact ⟨hu,hle,hru,by omega,by omega,hs⟩
  rw [he]
  exact card_cells_equiv hp hp (fun _ h => h.2.2.2.2.2.2)
    (fun _ h => h.1.2.2.2) (specialEquiv n 0 (by decide) (by omega))

theorem card_double_child (n : ℕ) (hn : 0 < n) :
    (cells (2*n) (doubleChild n)).card = (cells (2*n) (positiveMixed (2*n))).card := by
  have hp : 0 < 2*n := by omega
  have he : doubleChild n = special (2*n) 1 := by
    funext p
    apply propext
    unfold doubleChild special
    constructor
    · rintro ⟨hv,hle,hru,hrv,hrw,hs⟩
      exact ⟨by omega,hv,hle,hru,by omega,by omega,hs⟩
    · rintro ⟨hu,hv,hle,hru,hrv,hrw,hs⟩
      exact ⟨hv,hle,hru,by omega,by omega,hs⟩
  rw [he]
  exact card_cells_equiv hp hp (fun _ h => h.2.2.2.2.2.2)
    (fun _ h => h.1.2.2.2) (specialEquiv (2*n) 1 (by decide) (by omega))

theorem card_odd_parent (n : ℕ) (hn : n % 2 = 1) :
    (cells n (positiveMixed n)).card =
      (marked n (positiveOdd n) (oddParent n)).card := by
  have hp : 0 < n := by omega
  rw [← card_odd_child n hn, ← card_cells_equiv hp hp (fun _ h => h.2.2)
    (fun _ h => h.2.2.2.2.2) (oddEquiv n hn)]
  apply card_marked hp
  · exact fun _ h => h.1.2
  · exact fun _ h => h.1.le
  · rintro ⟨a,b,c⟩ ⟨hab,⟨ha,hb,hc⟩,hs⟩
    dsimp only at hab ha hb hc hs
    have hsorted := put_sorted (c := c) hab.le
    have hsurf : surface n (put a b c).1 (put a b c).2.1 (put a b c).2.2 :=
      (area_put a b c).trans hs
    refine ⟨⟨?_,hsorted.1,hsorted.2,hsurf⟩,?_⟩ <;> unfold put <;>
      split <;> (first | split | skip) <;> simp [allOdd,ha,hb,hc] <;> omega

theorem card_double_parent (n : ℕ) (hn : 0 < n) :
    (cells (2*n) (positiveMixed (2*n))).card =
      (marked n (sortedNonnegative n) (doubleParent n)).card := by
  have hp : 0 < 2*n := by omega
  rw [← card_double_child n hn, ← card_cells_equiv hn hp (fun _ h => h.2.2.2)
    (fun _ h => h.2.2.2.2.2) (doubleEquiv n)]
  apply card_marked hn (fun _ h => h) (fun _ h => h.2.1)
  rintro ⟨a,b,c⟩ ⟨ha,hab,hmod,hs⟩
  exact ⟨(put_sorted hab).1,(put_sorted hab).2,(area_put a b c).trans hs⟩

theorem card_positive (n : ℕ) (hn : 0 < n) :
    OMA.S_oeis_a375785.a n = (cells n (sortedPositive n)).card := by
  classical
  unfold OMA.S_oeis_a375785.a
  congr 1
  ext p
  rcases p with ⟨x,y,z⟩
  rw [mem_cells hn (fun _ h => h.2.2.2)]
  simp only [mem_filter, mem_product, mem_Icc, sortedPositive, surface, area, Prod.fst, Prod.snd]
  constructor
  · omega
  · rintro ⟨hx,hxy,hyz,hs⟩
    have ha := Nat.mul_le_mul_left x hxy
    have hb := Nat.mul_le_mul_left x (hxy.trans hyz)
    have hc := Nat.mul_le_mul hxy (hxy.trans hyz)
    have hd := Nat.mul_le_mul_left y hyz
    have hxn : x ≤ n := (Nat.pow_le_pow_iff_left (show 2 ≠ 0 by decide)).mp (by
      nlinarith only [hs,ha,hb,hc])
    have hyn : y ≤ 2*n := (Nat.pow_le_pow_iff_left (show 2 ≠ 0 by decide)).mp (by
      nlinarith only [hs,hd,Nat.zero_le (n^2),Nat.zero_le (x*y),Nat.zero_le (x*z)])
    have hzn := (area_bounds hn (show surface n x y z from hs)).2.2
    omega

theorem card_partition (n r : ℕ) (hn : 0 < n) (hr : r ≤ 1) (hnr : n%2 = 1-r) :
    (cells n (sortedPositive n)).card =
      (cells n (fun p => sortedPositive n p ∧
        p.1%2=1-r ∧ p.2.1%2=1-r ∧ p.2.2%2=1-r)).card +
      (cells n (positiveMixed n)).card := by
  classical
  change (cells n (sortedPositive n)).card = _ +
    (cells n (fun p => sortedPositive n p ∧ mixing p)).card
  rw [cells_and, cells_and]
  have hEq : ((cells n (sortedPositive n)).filter
      (fun p => p.1%2=1-r ∧ p.2.1%2=1-r ∧ p.2.2%2=1-r)) =
      ((cells n (sortedPositive n)).filter fun p => ¬ mixing p) := by
    ext p
    simp only [mem_filter]
    rcases p with ⟨x,y,z⟩
    constructor <;> rintro ⟨hp,hq⟩
    · exact ⟨hp, (parity_cases ((mem_cells hn (fun _ h => h.2.2.2) _).mp hp).2.2.2
        r hr hnr).1.mp hq⟩
    · exact ⟨hp, (parity_cases ((mem_cells hn (fun _ h => h.2.2.2) _).mp hp).2.2.2
        r hr hnr).1.mpr hq⟩
  rw [hEq, add_comm]
  exact (card_filter_add_card_filter_not (s := cells n (sortedPositive n)) mixing).symm

end OMA.CuboidParity
namespace OMA.CuboidParity

open Finset
open scoped BigOperators

noncomputable def oddWeight (n : ℕ) (p : Triple) : ℕ := by
  classical
  exact 1 + ((edges p).filter fun c => oddParent n (pick p c)).card

noncomputable def doubleWeight (n : ℕ) (p : Triple) : ℕ := by
  classical
  exact ((edges p).filter fun c => doubleParent n (pick p c)).card

theorem odd_weight {n x y z : ℕ} (hp : positiveOdd n (x,y,z)) :
    Odd (oddWeight n (x,y,z)) ↔ x = y ∧ y = z := by
  classical
  obtain ⟨⟨hx,hxy,hyz,hs⟩,ha,hb,hc⟩ := hp
  dsimp only at hx hxy hyz hs ha hb hc
  have hf : ((edges (x,y,z)).filter fun c => oddParent n (pick (x,y,z) c)) =
      ((edges (x,y,z)).filter fun c => (pick (x,y,z) c).1 < (pick (x,y,z) c).2.1) := by
    apply filter_congr
    intro c hc'
    have hs' : surface n (pick (x,y,z) c).1 (pick (x,y,z) c).2.1 c := (area_pick hc').trans hs
    have ht : allOdd (pick (x,y,z) c) := by
      simp only [edges,mem_insert,mem_singleton] at hc'
      rcases hc' with h | h | h <;> subst c <;>
        simp only [pick] <;> split_ifs <;>
        simp [allOdd,ha,hb,hc]
    simp only [oddParent, pick_mark, ht, hs', and_true]
  rw [oddWeight,hf]
  by_cases h1 : x = y
  · subst y
    by_cases h2 : x = z
    · subst z
      simp [edges,pick]
    · have hzx : z ≠ x := Ne.symm h2
      have hxz : x < z := lt_of_le_of_ne hyz h2
      simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hzx,hxz,h2]
  · by_cases h2 : y = z
    · subst z
      have hyx : y ≠ x := Ne.symm h1
      have hxy' : x < y := lt_of_le_of_ne hxy h1
      simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hyx,hxy',h1]
    · have hyx : y ≠ x := Ne.symm h1
      have hzy : z ≠ y := Ne.symm h2
      have hxy' : x < y := lt_of_le_of_ne hxy h1
      have hyz' : y < z := lt_of_le_of_ne hyz h2
      have hxz : x < z := hxy'.trans hyz'
      have hzx : z ≠ x := (Nat.ne_of_lt hxz).symm
      have hh : x ∉ ({y,z} : Finset ℕ) := by simp [h1,Nat.ne_of_lt hxz]
      simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hyx,hzy,hzx,hxy',hyz',hxz,h1,h2,
        Finset.card_insert_of_notMem hh, Finset.card_pair h2]
      exact ⟨2, rfl⟩

-- In the odd case, a noncube all-odd triple and its mixed descendants contribute
-- either two or four cuboids. The cube itself contributes one.
theorem odd_base (n : ℕ) (hn : n%2 = 1) : Odd (OMA.S_oeis_a375785.a n) := by
  classical
  have hp : 0 < n := by omega
  have he : (cells n (sortedPositive n)).card = (cells n (positiveOdd n)).card +
      (cells n (positiveMixed n)).card := by
    exact card_partition n 0 hp (by decide) (by omega)
  rw [card_positive n hp,he,card_odd_parent n hn]
  have hs : (cells n (positiveOdd n)).card + (marked n (positiveOdd n) (oddParent n)).card =
      ∑ p ∈ cells n (positiveOdd n), oddWeight n p := by
    unfold marked oddWeight
    rw [Finset.card_sigma,Finset.sum_add_distrib,← Finset.card_eq_sum_ones]
  rw [hs, Finset.odd_sum_iff_odd_card_odd]
  have hsingleton : ((cells n (positiveOdd n)).filter fun p => Odd (oddWeight n p)) = {(n,n,n)} := by
    ext p
    rcases p with ⟨x,y,z⟩
    rw [mem_filter, mem_cells hp (fun _ h => h.1.2.2.2)]
    simp only [mem_singleton]
    constructor
    · rintro ⟨hc,hw⟩
      obtain ⟨hxy,hyz⟩ := (odd_weight hc).mp hw
      subst z
      subst y
      have hsx : x^2 = n^2 := by
        have hh := hc.1.2.2.2
        change area x x x = 3 * n ^ 2 at hh
        unfold area at hh
        nlinarith only [hh]
      have hx : x = n := Nat.pow_left_injective (by decide : 2 ≠ 0) hsx
      simp [hx]
    · intro he
      rw [he]
      have hc : positiveOdd n (n,n,n) :=
        ⟨⟨hp,le_rfl,le_rfl,by unfold surface area; ring⟩,hn,hn,hn⟩
      exact ⟨hc,(odd_weight hc).mpr ⟨rfl,rfl⟩⟩
  rw [hsingleton, Finset.card_singleton]
  decide

-- A parent has an odd number of admissible marks precisely when its two
-- same-parity positive edges coincide, or its marked edge is zero.
theorem double_weight {n x y z : ℕ} (hn : 0 < n)
    (hp : sortedNonnegative n (x,y,z)) :
    Odd (doubleWeight n (x,y,z)) ↔ exception n (x,y,z) := by
  classical
  obtain ⟨hxy,hyz,hs⟩ := hp
  dsimp only at hxy hyz hs
  have hy : 0 < y := by
    by_contra! hy'
    have hy0 : y = 0 := by omega
    have hx0 : x = 0 := by omega
    have hbig : 0 < 3*n^2 := by positivity
    unfold surface area at hs
    simp [hx0,hy0] at hs
    omega
  have hz : 0 < z := by omega
  have hf : ((edges (x,y,z)).filter fun c => doubleParent n (pick (x,y,z) c)) =
      ((edges (x,y,z)).filter fun c => 0 < (pick (x,y,z) c).1 ∧
        (pick (x,y,z) c).1 % 2 ≠ (pick (x,y,z) c).2.1 % 2) := by
    apply filter_congr
    intro c hc
    have hs' : surface n (pick (x,y,z) c).1 (pick (x,y,z) c).2.1 c := (area_pick hc).trans hs
    simp only [doubleParent, pick_order hxy hyz, pick_mark, hs', and_true, true_and]
  rw [doubleWeight,hf]
  change Odd _ ↔ sortedNonnegative n (x,y,z) ∧
    ((x = 0 ∧ y % 2 ≠ z % 2) ∨ (0 < x ∧ mixing (x,y,z) ∧ (x=y ∨ y=z)))
  simp only [show sortedNonnegative n (x,y,z) from ⟨hxy,hyz,hs⟩, true_and]
  by_cases hx : x = 0
  · subst x
    by_cases hzy : z = y
    · subst z
      simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hy.ne',hy]
    · by_cases hpar : y % 2 = z % 2 <;>
        simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hy.ne',hz.ne',hy,hz,hpar,hzy]
  · have hx' : 0 < x := by omega
    by_cases h1 : x = y
    · subst y
      by_cases h2 : x = z
      · subst z
        simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hx,hx',mixing]
      · have hzx : z ≠ x := Ne.symm h2
        by_cases hpar : x % 2 = z % 2 <;>
          simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hx,hx',hzx,h2,hpar,mixing]
    · by_cases h2 : y = z
      · subst z
        have hyx : y ≠ x := Ne.symm h1
        by_cases hpar : x % 2 = y % 2 <;>
          simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hx,hx',hyx,h1,hpar,mixing]
      · have hyx : y ≠ x := Ne.symm h1
        have hzy : z ≠ y := Ne.symm h2
        have hzx : z ≠ x := by omega
        have hxz : x ≠ z := by omega
        rcases (show x % 2 = 0 ∨ x % 2 = 1 by omega) with hrx | hrx <;>
          rcases (show y % 2 = 0 ∨ y % 2 = 1 by omega) with hry | hry <;>
          rcases (show z % 2 = 0 ∨ z % 2 = 1 by omega) with hrz | hrz <;>
            simp [edges,pick,Finset.filter_insert,Finset.filter_singleton,hx,hx',hy,hyx,hzy,hzx,hxz,h1,h2,
              hrx,hry,hrz,Finset.card_pair, Nat.not_odd_iff_even, mixing]

theorem even_mixed_double (n : ℕ) (hn : 0 < n)
    (he : Even ((cells n (exception n)).card)) :
    Even ((cells (2*n) (positiveMixed (2*n))).card) := by
  classical
  rw [card_double_parent n hn,marked,Finset.card_sigma]
  change Even (∑ p ∈ cells n (sortedNonnegative n), doubleWeight n p)
  rw [Finset.even_sum_iff_even_card_odd]
  convert he using 1
  congr 1
  ext p
  rcases p with ⟨x,y,z⟩
  rw [mem_filter,mem_cells hn (fun _ h => h.2.2),
    mem_cells hn (fun _ h => h.1.2.2)]
  constructor
  · rintro ⟨hp,ho⟩
    exact (double_weight hn hp).mp ho
  · intro hp
    exact ⟨hp.1,(double_weight hn hp.1).mpr hp⟩

theorem card_positive_even (n : ℕ) (hn : 0 < n) :
    (cells (2*n) (positiveEven (2*n))).card = (cells n (sortedPositive n)).card := by
  have hp : 0 < 2*n := by omega
  apply card_cells_equiv hp hn (fun _ h => h.1.2.2.2) (fun _ h => h.2.2.2)
  refine ⟨?_,?_,?_,?_⟩
  · intro p
    refine ⟨(p.val.1/2,p.val.2.1/2,p.val.2.2/2),?_⟩
    rcases p with ⟨⟨x,y,z⟩,⟨hx,hxy,hyz,hs⟩,ex,ey,ez⟩
    dsimp only at hx hxy hyz hs ex ey ez
    dsimp only [sortedPositive]
    refine ⟨by omega,by omega,by omega,?_⟩
    have ehx : x = 2*(x/2) := by omega
    have ehy : y = 2*(y/2) := by omega
    have ehz : z = 2*(z/2) := by omega
    generalize x/2 = a at ehx ⊢
    generalize y/2 = b at ehy ⊢
    generalize z/2 = c at ehz ⊢
    unfold surface area at hs ⊢
    rw [ehx,ehy,ehz] at hs
    nlinarith only [hs]
  · intro p
    refine ⟨(2*p.val.1,2*p.val.2.1,2*p.val.2.2),?_⟩
    rcases p with ⟨⟨a,b,c⟩,ha,hab,hbc,hs⟩
    dsimp only at ha hab hbc hs
    dsimp only [positiveEven,sortedPositive]
    refine ⟨⟨by omega,by omega,by omega,?_⟩,by omega,by omega,by omega⟩
    unfold surface area at hs ⊢
    nlinarith only [hs]
  · rintro ⟨⟨x,y,z⟩,h,ex,ey,ez⟩
    dsimp only at ex ey ez
    apply Subtype.ext
    change (2*(x/2),2*(y/2),2*(z/2)) = (x,y,z)
    simp only [Prod.mk.injEq]
    omega
  · rintro ⟨⟨a,b,c⟩,h⟩
    apply Subtype.ext
    change ((2*a)/2,(2*b)/2,(2*c)/2) = (a,b,c)
    simp only [Prod.mk.injEq]
    omega

theorem parity_double (n : ℕ) (hn : 0 < n)
    (he : Even ((cells n (exception n)).card)) :
    Odd (OMA.S_oeis_a375785.a (2*n)) ↔ Odd (OMA.S_oeis_a375785.a n) := by
  have hp : 0 < 2*n := by omega
  have hc : (cells (2*n) (sortedPositive (2*n))).card =
      (cells (2*n) (positiveEven (2*n))).card +
        (cells (2*n) (positiveMixed (2*n))).card := by
    exact card_partition (2*n) 1 hp (by decide) (by omega)
  rw [card_positive (2*n) hp,card_positive n hn,hc,card_positive_even n hn]
  have hm := Nat.even_iff.mp (even_mixed_double n hn he)
  repeat rw [Nat.odd_iff]
  omega

end OMA.CuboidParity
namespace OMA.CuboidParity

open Finset

def factors (n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 (3*n^2) ×ˢ Finset.Icc 1 (3*n^2)).filter fun p : ℕ × ℕ =>
    p.1 ≤ p.2 ∧ p.1 * p.2 = 3*n^2 ∧ p.1 % 2 ≠ p.2 % 2

theorem mem_factors {n a b : ℕ} :
    (a,b) ∈ factors n ↔ 0 < a ∧ a ≤ b ∧ a*b = 3*n^2 ∧ a%2 ≠ b%2 := by
  simp only [factors, mem_filter, mem_product, mem_Icc, Prod.fst, Prod.snd]
  constructor
  · rintro ⟨⟨⟨ha,_⟩,_⟩,hle,hprod,hpar⟩
    exact ⟨ha,hle,hprod,hpar⟩
  · rintro ⟨ha,hle,hprod,hpar⟩
    have hb : 0 < b := by omega
    have h1 := Nat.le_mul_of_pos_right a hb
    have h2 := Nat.le_mul_of_pos_left b ha
    exact ⟨⟨⟨ha,hprod ▸ h1⟩,⟨hb,hprod ▸ h2⟩⟩,hle,hprod,hpar⟩

def rectangle (n : ℕ) (p : Triple) : Prop :=
  sortedNonnegative n p ∧ p.1=0 ∧ p.2.1%2 ≠ p.2.2%2

def tied (n : ℕ) (p : Triple) : Prop :=
  sortedPositive n p ∧ mixing p ∧ (p.1=p.2.1 ∨ p.2.1=p.2.2)

theorem rectangle_even (n : ℕ) (hn : 0 < n) : Even ((cells n (rectangle n)).card) := by
  have hs : ∀ p, rectangle n p → surface n p.1 p.2.1 p.2.2 := fun _ h => h.1.2.2
  have hcard : (cells n (rectangle n)).card = (factors n).card := by
    refine Finset.card_nbij' Prod.snd (fun p : ℕ × ℕ => (0,p.1,p.2)) ?_ ?_ ?_ ?_
    · rintro ⟨x,y,z⟩ hp
      obtain ⟨⟨hxy,hyz,h⟩,hx,hmod⟩ := (mem_cells hn hs _).mp hp
      dsimp only at hx hxy hyz h hmod
      subst x
      simp [surface,area] at h
      have hp' : 0 < 3*n^2 := by positivity
      have hy : 0 < y := by
        by_contra! hy
        have h0 : y = 0 := by omega
        simp [h0] at h
        omega
      exact mem_factors.mpr ⟨hy,hyz,h,hmod⟩
    · rintro ⟨a,b⟩ hp
      obtain ⟨ha,hab,hprod,hmod⟩ := mem_factors.mp hp
      exact (mem_cells hn hs _).mpr ⟨⟨Nat.zero_le _,hab,by simpa [surface,area]⟩,rfl,hmod⟩
    · rintro ⟨x,y,z⟩ hp
      have hx := ((mem_cells hn hs _).mp hp).2.1
      change x = 0 at hx
      subst x
      rfl
    · rintro ⟨a,b⟩ _
      rfl
  rw [hcard]
  exact oppositeFactorPairs_even n hn

def repeated (p : Triple) : ℕ × ℕ :=
  if p.1 = p.2.1 then (p.1,p.2.2) else (p.2.1,p.1)

theorem tied_read {n x y z : ℕ} (hp : tied n (x,y,z)) :
    let d := (repeated (x,y,z)).1
    let t := (repeated (x,y,z)).2
    0 < d ∧ 0 < t ∧ d%2 ≠ t%2 ∧ surface n d d t ∧ put d d t = (x,y,z) := by
  obtain ⟨⟨hx,hxy,hyz,hs⟩,hm,ht⟩ := hp
  dsimp only at hx hxy hyz hs ht
  rcases ht with h | h
  · subst y
    have hmod : x%2 ≠ z%2 := by simpa [mixing] using hm
    have hne : z ≠ x := by rintro rfl; contradiction
    have hle : ¬ z ≤ x := by omega
    simp [repeated,put,hle,hs,hx,show 0 < z by omega,hmod]
  · subst z
    have hmod : y%2 ≠ x%2 := by simpa [mixing,ne_comm] using hm
    have hne : x ≠ y := by rintro rfl; contradiction
    have hs' : surface n y y x := by unfold surface area at *; nlinarith only [hs]
    simp [repeated,put,hxy,hx,show 0 < y by omega,hmod,hne,hs']

theorem tied_build {n d t : ℕ} (hd : 0 < d) (ht : 0 < t)
    (hpar : d%2 ≠ t%2) (hs : surface n d d t) :
    tied n (put d d t) ∧ repeated (put d d t) = (d,t) := by
  have hne : d ≠ t := by rintro rfl; contradiction
  unfold put
  by_cases he : t ≤ d
  · have hst : surface n t d d := by unfold surface area at *; nlinarith only [hs]
    simp [if_pos he,tied,sortedPositive,mixing,repeated,hst,ht,he,hne.symm,hpar.symm]
  · simp [if_neg he,tied,sortedPositive,mixing,repeated,hs,hd,show d ≤ t by omega,hpar]

theorem tie_parity {n d t : ℕ} (hs : surface n d d t) : d%2 = n%2 := by
  have he := @surface_rem 2 n d d t hs
  rcases (show d%2=0 ∨ d%2=1 by omega) with hd | hd <;>
    rcases (show t%2=0 ∨ t%2=1 by omega) with ht | ht <;>
    rcases (show n%2=0 ∨ n%2=1 by omega) with hn | hn <;>
    rw [hd, ht, hn] at he <;>
    norm_num [area, Nat.ModEq] at he <;>
    omega

-- Write the tied surface equation as d(d+2t)=3n². At even n a mixed
-- tied triple has d even and corresponds to factors d/2 and d/2+t.
theorem tied_even (n : ℕ) (hn : 0 < n) : Even ((cells n (tied n)).card) := by
  have hsurf : ∀ p, tied n p → surface n p.1 p.2.1 p.2.2 := fun _ h => h.1.2.2.2
  by_cases hnmod : n%2 = 0
  · let k := n/2
    have hkn : n = 2*k := by dsimp [k]; omega
    have hk : 0 < k := by omega
    have hcard : (cells n (tied n)).card = (factors k).card := by
      refine Finset.card_nbij'
        (fun p => ((repeated p).1/2,(repeated p).1/2+(repeated p).2))
        (fun p : ℕ × ℕ => put (2*p.1) (2*p.1) (p.2-p.1)) ?_ ?_ ?_ ?_
      · rintro ⟨x,y,z⟩ hp
        change ((repeated (x,y,z)).1/2,(repeated (x,y,z)).1/2+(repeated (x,y,z)).2) ∈ factors k
        have h := tied_read ((mem_cells hn hsurf _).mp hp)
        dsimp only at h
        generalize (repeated (x,y,z)).1 = d at h ⊢
        generalize (repeated (x,y,z)).2 = t at h ⊢
        obtain ⟨hd,ht,hpar,hs,_⟩ := h
        have hdmod : d%2=0 := (tie_parity hs).trans hnmod
        have hdf : d = 2*(d/2) := by omega
        apply mem_factors.mpr
        refine ⟨by omega,by omega,?_,by omega⟩
        generalize d/2 = u at hdf ⊢
        unfold surface area at hs
        rw [hkn,hdf] at hs
        nlinarith only [hs]
      · rintro ⟨u,v⟩ hp
        obtain ⟨hu,huv,hprod,hpar⟩ := mem_factors.mp hp
        apply (mem_cells hn hsurf _).mpr
        have hd : 0 < 2*u := by omega
        have ht : 0 < v-u := by omega
        have hpar' : (2*u)%2 ≠ (v-u)%2 := by omega
        have hs : surface n (2*u) (2*u) (v-u) := by
          have hv : v = u+(v-u) := by omega
          generalize v-u = t at hv ⊢
          rw [hkn]
          unfold surface area
          rw [hv] at hprod
          nlinarith only [hprod]
        exact (tied_build hd ht hpar' hs).1
      · rintro ⟨x,y,z⟩ hp
        have h := tied_read ((mem_cells hn hsurf _).mp hp)
        dsimp only at h ⊢
        generalize (repeated (x,y,z)).1 = d at h ⊢
        generalize (repeated (x,y,z)).2 = t at h ⊢
        obtain ⟨hd,ht,hpar,hs,he⟩ := h
        have hdmod : d%2=0 := (tie_parity hs).trans hnmod
        rw [show 2*(d/2) = d by omega, show d/2+t-d/2=t by omega]
        exact he
      · rintro ⟨u,v⟩ hp
        obtain ⟨hu,huv,hprod,hpar⟩ := mem_factors.mp hp
        dsimp only
        have hd : 0 < 2*u := by omega
        have ht : 0 < v-u := by omega
        have hpar' : (2*u)%2 ≠ (v-u)%2 := by omega
        have hs : surface n (2*u) (2*u) (v-u) := by
          have hv : v = u+(v-u) := by omega
          generalize v-u = t at hv ⊢
          rw [hkn]
          unfold surface area
          rw [hv] at hprod
          nlinarith only [hprod]
        rw [(tied_build hd ht hpar' hs).2]
        simp only [Prod.mk.injEq]
        omega
    rw [hcard]
    exact oppositeFactorPairs_even k hk
  · have hnodd : n%2=1 := by omega
    have hempty : cells n (tied n) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      rintro ⟨x,y,z⟩ hp
      have h := tied_read ((mem_cells hn hsurf _).mp hp)
      dsimp only at h
      generalize (repeated (x,y,z)).1 = d at h
      generalize (repeated (x,y,z)).2 = t at h
      obtain ⟨hd,ht,hpar,hs,_⟩ := h
      have hdo : d%2=1 := (tie_parity hs).trans hnodd
      have hd4 : d^2%4 = 1 := by have hh := odd_sq_mod_eight d hdo; omega
      have hn4 : n^2%4 = 1 := by have hh := odd_sq_mod_eight n hnodd; omega
      have hte : t=2*(t/2) := by omega
      have hs' : d^2+4*(d*(t/2))=3*n^2 := by
        generalize t/2 = u at hte ⊢
        unfold surface area at hs
        rw [hte] at hs
        nlinarith only [hs]
      omega
    simp [hempty]

theorem exception_even (n : ℕ) (hn : 0 < n) : Even ((cells n (exception n)).card) := by
  classical
  have hr : ∀ p, rectangle n p → surface n p.1 p.2.1 p.2.2 := fun _ h => h.1.2.2
  have ht : ∀ p, tied n p → surface n p.1 p.2.1 p.2.2 := fun _ h => h.1.2.2.2
  have he : ∀ p, exception n p → surface n p.1 p.2.1 p.2.2 := fun _ h => h.1.2.2
  have hh : cells n (exception n) = cells n (rectangle n) ∪ cells n (tied n) := by
    ext p
    rw [mem_union,mem_cells hn he,mem_cells hn hr,mem_cells hn ht]
    unfold exception rectangle tied sortedNonnegative sortedPositive
    tauto
  have hd : Disjoint (cells n (rectangle n)) (cells n (tied n)) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have h1 := ((mem_cells hn hr p).mp hp).2.1
    have h2 := ((mem_cells hn ht p).mp hq).1.1
    omega
  rw [hh,Finset.card_union_of_disjoint hd]
  exact (rectangle_even n hn).add (tied_even n hn)

end OMA.CuboidParity

theorem OMA.solution : type_of% @OMA.S_oeis_a375785.main := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hodd : n%2=1
    · exact OMA.CuboidParity.odd_base n hodd
    · have hpos : 0 < n/2 := by omega
      have hsmall : n/2 < n := by omega
      have htwo : n = 2*(n/2) := by omega
      have hrec := ih (n/2) hsmall (by omega)
      have hstep := OMA.CuboidParity.parity_double (n/2) hpos
        (OMA.CuboidParity.exception_even (n/2) hpos)
      nth_rw 1 [htwo]
      exact hstep.mpr hrec
