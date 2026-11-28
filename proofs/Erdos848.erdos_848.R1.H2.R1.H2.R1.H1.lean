import OMAReductions.R_Erdos848_erdos_848_R1_H2_R1_H2_R1
import Mathlib

/-!
# Crossed residue counts for Erdős 848

For N ≥ 160000000 and a fixed pivot in class 7 or 18 modulo 25, we bound
the number of opposite-class inputs for which the product plus one fails
to be squarefree. The bound is uniform in N and in the pivot.

The modular sieve, unitary divisor keys, and root tags adapt Deldor14's
proof in open-math-agents PR 8925. The transformed-root spacing argument
is due to Alex Chengyu Li. The modular sieve incorporates Apache-2.0 work
by Raymond Jung, Claude Opus 4.5, GPT-5.2 Pro/xHigh, Gemini 3.0 and Aristotle.
https://github.com/GuillaumeBAUD-coder/open-math-agents/pull/8925
https://github.com/crabsatellite/erdos-848-squarefree-product/blob/011a0d98f54fb31953a8f0896b4555a70ae56b83/paper/erdos_848_kernel_checked_exact_extremal_bound.tex
https://github.com/The-Obstacle-Is-The-Way/erdos-banger/blob/1cc2ac8e9d70516e979733c6ea5c4d2eb652d1f5/formal/lean/Erdos/848.lean

Here the residue of the complementary divisor rules out d = 1, so we can
split the prime-square sieve at N / 48. A finite quadratic-residue count
for d ≤ 2304 and a bound for the remaining prime divisors of the pivot
give the same large-prime estimate at every scale.
-/

open scoped BigOperators Finset Nat.Prime

namespace CrossedResidue

namespace Unitary

private theorem coprime_factor_ext {a c a' c' : ℕ}
    (pos : 0 < a*c) (eq : a*c=a'*c') (ha : a.Coprime c) (ha' : a'.Coprime c')
    (hs : a.primeFactors=a'.primeFactors) : a=a' := by
  have pos' : 0 < a'*c' := eq ▸ pos
  have ac := Nat.pos_of_mul_pos_right pos
  have av := Nat.pos_of_mul_pos_left pos
  have ac' := Nat.pos_of_mul_pos_right pos'
  have av' := Nat.pos_of_mul_pos_left pos'
  have h : a.Coprime c' := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha'.disjoint_primeFactors)
  have h' : a'.Coprime c := (Nat.disjoint_primeFactors (by positivity) (by positivity)).mp
    (hs ▸ ha.disjoint_primeFactors)
  apply Nat.dvd_antisymm
  · exact h.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a c)
  · exact h'.dvd_of_dvd_mul_right (eq ▸ dvd_mul_right a' c')

/-- Count divisors of b with gcd at most two with the complementary factor. -/
theorem count_unitary_keys (b : ℕ) (bpos : 0 < b) :
    (b.divisors.filter (fun g => (Nat.gcd g (b/g)) ∣ 2)).card ≤ 2 * 2^b.primeFactors.card := by
  classical
  let k (g : ℕ) := Nat.gcd g (b/g)
  let a (g : ℕ) := g/k g
  let c (g : ℕ) := (b/g)/k g
  let D := b.divisors.filter (fun g => k g ∣ 2)
  let K := (Finset.Icc 1 2).product b.primeFactors.powerset
  let code (g : ℕ) := (k g, (a g).primeFactors)
  have gd {g : ℕ} (hg : g ∈ D) : g ∣ b := (Nat.mem_divisors.mp (Finset.mem_filter.mp hg).1).1
  have kg {g : ℕ} (hg : g ∈ D) : 0 < k g := Nat.gcd_pos_of_pos_left _ (Nat.pos_of_dvd_of_pos (gd hg) bpos)
  have ag (g : ℕ) : a g*k g=g := Nat.div_mul_cancel (Nat.gcd_dvd_left ..)
  have cg (g : ℕ) : c g*k g=b/g := Nat.div_mul_cancel (Nat.gcd_dvd_right ..)
  have B {g : ℕ} (hg : g ∈ D) : (a g*c g)*(k g*k g)=b := calc
    _ = (a g*k g)*(c g*k g) := by ring
    _ = b := by rw [ag,cg,Nat.mul_div_cancel' (gd hg)]
  have count : D.card ≤ K.card := by
    apply Finset.card_le_card_of_injOn code
    · intro g hg
      refine Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨kg hg,?_⟩, Finset.mem_powerset.mpr ?_⟩
      · exact Nat.le_of_dvd (by decide) (Finset.mem_filter.mp hg).2
      · exact Nat.primeFactors_mono ((Nat.div_dvd_of_dvd (Nat.gcd_dvd_left ..)).trans (gd hg)) bpos.ne'
    · intro x hx y hy he
      have hk : k x=k y := congrArg Prod.fst he
      have hs : (a x).primeFactors=(a y).primeFactors := congrArg Prod.snd he
      have e : a x*c x=a y*c y := by
        apply Nat.eq_of_mul_eq_mul_right (Nat.mul_pos (kg hx) (kg hx))
        rw [B hx,hk,B hy]
      have pp : 0 < a x*c x := Nat.pos_of_mul_pos_right (show 0 < (a x*c x)*(k x*k x) by rw [B hx]; exact bpos)
      have ax := coprime_factor_ext pp e (Nat.coprime_div_gcd_div_gcd (kg hx)) (Nat.coprime_div_gcd_div_gcd (kg hy)) hs
      rw [← ag x,← ag y,ax,hk]
  simpa [K, Finset.card_product] using count

end Unitary

namespace RootClass

private theorem root_factor {B D R X T U : ℤ}
    (hr : D*R^2=B*T+1) (hx : D*X^2=B*U+1) : B ∣ (X-R)*(X+R) := by
  refine ⟨R^2*U-X^2*T, ?_⟩
  linear_combination R^2*hx - X^2*hr

private theorem gcd_times_sum {B R X : ℤ} (hx : B ∣ (X-R)*(X+R)) :
    B ∣ (Int.gcd B (X-R) : ℤ)*(X+R) := by
  obtain ⟨q,hq⟩ := hx
  refine ⟨Int.gcdA B (X-R)*(X+R)+Int.gcdB B (X-R)*q, ?_⟩
  rw [Int.gcd_eq_gcd_ab]
  linear_combination Int.gcdB B (X-R)*hq

theorem roots_in_class {B D R X Y T U V : ℤ}
    (hr : D*R^2=B*T+1) (hx : D*X^2=B*U+1) (hy : D*Y^2=B*V+1)
    (hg : Int.gcd B (X-R) = Int.gcd B (Y-R)) : B ∣ 2*(Y-X) := by
  let g : ℤ := Int.gcd B (X-R)
  have h₁ : B ∣ g*(X+R) := gcd_times_sum (root_factor hr hx)
  have h₂ : B ∣ g*(Y+R) := by simpa only [g,hg] using gcd_times_sum (root_factor hr hy)
  have h₃ : B ∣ g*(Y-X) := by
    convert! dvd_sub h₂ h₁ using 1
    ring
  have gx : g ∣ X-R := Int.gcd_dvd_right ..
  have gy : g ∣ Y-R := by simpa only [g,hg] using Int.gcd_dvd_right B (Y-R)
  have gxy : g ∣ Y-X := by
    convert! dvd_sub gy gx using 1
    ring
  have plus : B ∣ (Y-X)*(X+R) := h₁.trans (mul_dvd_mul_right gxy _)
  have minus : B ∣ (Y-X)*(X-R) := by
    rw [mul_comm (Y-X) (X-R)]
    exact h₃.trans (mul_dvd_mul_right gx _)
  have twice : B ∣ 2*R*(Y-X) := by
    convert! dvd_sub plus minus using 1
    ring
  obtain ⟨k,hk⟩ := twice
  refine ⟨D*R*k-2*(Y-X)*T,?_⟩
  linear_combination D*R*hk-2*(Y-X)*hr

theorem root_key_valid {b : ℕ} (bpos : 0 < b) {D R X T U : ℤ}
    (hr : D*R^2=(b : ℤ)*T+1) (hx : D*X^2=(b : ℤ)*U+1) :
    let g := Int.gcd (b : ℤ) (X-R)
    Nat.gcd g (b/g) ∣ 2 := by
  let g := Int.gcd (b : ℤ) (X-R)
  let h := b/g
  let k := Nat.gcd g h
  change k ∣ 2
  have gb : g ∣ b := by exact_mod_cast Int.gcd_dvd_left (b : ℤ) (X-R)
  have gpos := Nat.pos_of_dvd_of_pos gb bpos
  have gh : (g : ℤ)*(h : ℤ)=(b : ℤ) := by exact_mod_cast Nat.mul_div_cancel' gb
  have gs : (b : ℤ) ∣ (g : ℤ)*(X+R) := gcd_times_sum (root_factor hr hx)
  obtain ⟨q,hq⟩ := gs
  have hs : (h : ℤ) ∣ X+R := by
    refine ⟨q,mul_left_cancel₀ (show (g : ℤ) ≠ 0 by exact_mod_cast gpos.ne') ?_⟩
    rw [← mul_assoc,gh,hq]
  have kg : (k : ℤ) ∣ (g : ℤ) := by exact_mod_cast Nat.gcd_dvd_left g h
  have kh : (k : ℤ) ∣ (h : ℤ) := by exact_mod_cast Nat.gcd_dvd_right g h
  have km : (k : ℤ) ∣ X-R := kg.trans (Int.gcd_dvd_right ..)
  have kp : (k : ℤ) ∣ X+R := kh.trans hs
  have kr := dvd_sub kp km
  rw [show X+R-(X-R)=2*R by ring] at kr
  have kb : (k : ℤ) ∣ (b : ℤ) := kg.trans (by exact_mod_cast gb)
  have old : (k : ℤ) ∣ (2*R)*(D*R)-2*((b : ℤ)*T) :=
    dvd_sub (dvd_mul_of_dvd_left kr _) (dvd_mul_of_dvd_right (dvd_mul_of_dvd_left kb _) _)
  have two : (2 : ℤ) = (2*R)*(D*R)-2*((b : ℤ)*T) := by linear_combination -2*hr
  rw [← two] at old
  exact_mod_cast old

end RootClass

namespace Sieve

lemma dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv
    {p a b : ℕ} (hp : Nat.Prime p) (ha : ¬p ∣ a) :
    p ^ 2 ∣ (a * b + 1) ↔ (b : ZMod (p ^ 2)) = -((a : ZMod (p ^ 2))⁻¹) := by
  set n : ℕ := p ^ 2
  have hcop : Nat.Coprime a n := by
    simpa [n] using hp.coprime_pow_of_not_dvd (m := 2) ha
  have haUnit : IsUnit (a : ZMod n) := (ZMod.isUnit_iff_coprime a n).2 hcop
  constructor
  · intro hdiv
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 :=
      (ZMod.natCast_eq_zero_iff (a * b + 1) n).2 hdiv
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz
    have hprod : (a : ZMod n) * (b : ZMod n) = (-1 : ZMod n) := by
      simpa using (eq_neg_of_add_eq_zero_left hz')
    have hb : (b : ZMod n) = (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
      have hb0 := congrArg (fun x : ZMod n => (a : ZMod n)⁻¹ * x) hprod
      have hb1 :
          ((a : ZMod n)⁻¹ * (a : ZMod n)) * (b : ZMod n) =
            (a : ZMod n)⁻¹ * (-1 : ZMod n) := by
        simpa [mul_assoc] using hb0
      simpa [ZMod.inv_mul_of_unit (a : ZMod n) haUnit] using hb1
    simpa [n, mul_comm, mul_left_comm, mul_assoc] using hb
  · intro hb
    have hz' : (a : ZMod n) * (b : ZMod n) + 1 = 0 := by
      simp [hb, ZMod.mul_inv_of_unit (a : ZMod n) haUnit]
    have hz : ((a * b + 1 : ℕ) : ZMod n) = 0 := by
      simpa [n, Nat.cast_add, Nat.cast_mul, Nat.cast_one] using hz'
    exact (ZMod.natCast_eq_zero_iff (a * b + 1) n).1 hz

noncomputable section DensityLemmas

lemma card_filter_mod_eq_le (N m r : ℕ) :
    ((Finset.range N).filter (fun n => n ≡ r [MOD m])).card ≤ N / m + 1 := by
  have h_set :
      Finset.filter (fun n => n ≡ r [MOD m]) (Finset.range N) ⊆
        Finset.image (fun q => q * m + (r % m)) (Finset.range (N / m + 1)) := by
    intro n hn
    obtain ⟨hnlt,heq⟩ := Finset.mem_filter.mp hn
    have hnN := Finset.mem_range.mp hnlt
    refine Finset.mem_image.mpr ⟨n/m, Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hnN.le)), ?_⟩
    change n % m = r % m at heq
    rw [← heq, Nat.mul_comm (n/m) m, Nat.add_comm, Nat.mod_add_div]
  exact le_trans (Finset.card_le_card h_set) (Finset.card_image_le.trans (by norm_num))

lemma card_filter_modEq_and_modEq_le (N m n a b : ℕ) (hcop : Nat.Coprime m n) :
    ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤ N / (m * n) + 1 := by
  classical
  have hsub :
      (Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n]) ⊆
        (Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n]) := by
    intro x hx
    simp [Finset.mem_filter, Finset.mem_range] at hx ⊢
    refine ⟨hx.1, ?_⟩
    exact Nat.chineseRemainder_modEq_unique (co := hcop) hx.2.1 hx.2.2
  have hcard :
      ((Finset.range N).filter (fun x => x ≡ a [MOD m] ∧ x ≡ b [MOD n])).card ≤
        ((Finset.range N).filter (fun x => x ≡ Nat.chineseRemainder hcop a b [MOD m * n])).card :=
    Finset.card_le_card hsub
  exact le_trans hcard (card_filter_mod_eq_le N (m * n) (Nat.chineseRemainder hcop a b))

end DensityLemmas

lemma card_range_filter_mod25_eq (r : ℕ) (hr : r ≤ 24) (N : ℕ) :
    ((Finset.range N).filter (fun n => n % 25 = r)).card = (N + (24 - r)) / 25 := by
  classical
  have hr_lt : r < 25 := lt_of_le_of_lt hr (by decide : 24 < 25)
  set K : ℕ := (N + (24 - r)) / 25
  have hbij :
      ((Finset.range N).filter (fun n => n % 25 = r)).card = (Finset.range K).card := by
    refine (Finset.card_bij (s := Finset.range K) (t := (Finset.range N).filter (fun n => n % 25 = r))
      (i := fun k _hk => 25 * k + r) ?_ ?_ ?_).symm
    · intro k hk
      have hk' : k < K := by simpa [Finset.mem_range] using hk
      have hk1 : k + 1 ≤ K := Nat.succ_le_iff.2 hk'
      have hmul : 25 * (k + 1) ≤ 25 * K := Nat.mul_le_mul_left 25 hk1
      have hK : 25 * K ≤ N + (24 - r) := by
        simpa [K] using Nat.mul_div_le (N + (24 - r)) 25
      have hmul' : 25 * (k + 1) ≤ N + (24 - r) := le_trans hmul hK
      have hlt : 25 * k + r < N := by omega
      simp [Finset.mem_filter, Finset.mem_range, hlt, Nat.add_mod, hr_lt]
    · intro k₁ _hk₁ k₂ _hk₂ h
      have h' : 25 * k₁ = 25 * k₂ := Nat.add_right_cancel h
      exact Nat.mul_left_cancel (by decide : 0 < 25) h'
    · intro a ha
      have ha' : a < N ∧ a % 25 = r := by
        simpa [Finset.mem_filter, Finset.mem_range] using ha
      have ha_eq : 25 * (a / 25) + r = a := by
        have h := Nat.mod_add_div a 25
        simpa [ha'.2, Nat.add_comm, Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using h
      refine ⟨a / 25, ?_, ?_⟩
      · have hlt : 25 * (a / 25) + r < N := by simpa [ha_eq] using ha'.1
        have hmul : 25 * ((a / 25) + 1) ≤ N + (24 - r) := by omega
        have hle : a / 25 + 1 ≤ K := by
          have hmul' : (a / 25 + 1) * 25 ≤ N + (24 - r) := by
            simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using hmul
          have := (Nat.le_div_iff_mul_le (k0 := (by decide : 0 < 25))).2 hmul'
          simpa [K] using this
        have hltK : a / 25 < K := Nat.lt_of_lt_of_le (Nat.lt_succ_self _) hle
        simpa [Finset.mem_range] using hltK
      · exact ha_eq
  simpa [Finset.card_range, K] using hbij

open Filter Finset

def primeCutoff : ℕ := 2000

def primesUpTo (B : ℕ) : Finset ℕ :=
  (Finset.range (B + 1)).filter Nat.Prime

def no5PrimesCoarse : Finset ℕ :=
  (primesUpTo primeCutoff).filter (fun p => p ≠ 5)

/-- Each prime passes all trial divisions, including trial division by itself. -/
private def sievePass (p : ℕ) : Bool :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43].all fun d =>
    decide (d = 1 ∨ d = p ∨ ¬ d ∣ p)

private theorem prime_sievePass {p : ℕ} (hp : p.Prime) : sievePass p = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply decide_eq_true
  by_cases hd : d ∣ p
  · rcases (Nat.dvd_prime hp).mp hd with eq | eq
    · exact Or.inl eq
    · exact Or.inr (Or.inl eq)
  · exact Or.inr (Or.inr hd)

/-- Round each reciprocal square upward in units of 10⁻¹⁰. -/
private def upperWeight (p : ℕ) : ℕ := 10000000000 / (p*p) + 1

private def sieveTerm (keep : ℕ → Bool) (p : ℕ) : ℕ :=
  if 2 ≤ p ∧ keep p = true ∧ sievePass p = true then upperWeight p else 0

private def accumulate (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => accumulate f i + f i

private theorem accumulate_eq (f : ℕ → ℕ) (n : ℕ) :
    accumulate f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih => rw [accumulate, Finset.sum_range_succ, ih]

private theorem sum_reciprocal_bound (P : Finset ℕ) (pos : ∀ p ∈ P, 0 < p) :
    ∑ p ∈ P, (1:ℚ)/(p:ℚ)^2 ≤ ((∑ p ∈ P, upperWeight p : ℕ):ℚ) / 10000000000 := by
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_le_sum
  intro p hp
  have strict := Nat.lt_mul_div_succ 10000000000 (Nat.mul_pos (pos p hp) (pos p hp))
  have h : (10000000000 : ℚ) ≤ ((p*p:ℕ):ℚ) * (upperWeight p : ℚ) := by
    exact_mod_cast strict.le
  push_cast at h
  apply (div_le_div_iff₀ (sq_pos_of_pos (by exact_mod_cast pos p hp)) (by norm_num)).mpr
  linarith only [show (10000000000 : ℚ) ≤ (p:ℚ)^2 * (upperWeight p : ℚ) by simpa [sq] using h]

private theorem sieve_bound (P : Finset ℕ) (keep : ℕ → Bool)
    (member : ∀ p ∈ P, p ∈ Finset.range 2001 ∧ p.Prime ∧ keep p = true) :
    (∑ p ∈ P, (1:ℚ)/(p:ℚ)^2) ≤ (accumulate (sieveTerm keep) 2001 : ℚ) / 10000000000 := by
  have subset : P ⊆ Finset.range 2001 := fun p hp => (member p hp).1
  have total : ∑ p ∈ P, upperWeight p ≤ accumulate (sieveTerm keep) 2001 := by
    rw [accumulate_eq]
    calc
      ∑ p ∈ P, upperWeight p = ∑ p ∈ P, sieveTerm keep p := by
        apply Finset.sum_congr rfl
        intro p hp
        obtain ⟨_, pr, hkeep⟩ := member p hp
        simp only [sieveTerm, pr.two_le, hkeep, prime_sievePass pr, and_self, if_true]
      _ ≤ ∑ p ∈ Finset.range 2001, sieveTerm keep p :=
        Finset.sum_le_sum_of_subset_of_nonneg subset (fun _ _ _ => Nat.zero_le _)
  apply (sum_reciprocal_bound P (fun p hp => (member p hp).2.1.pos)).trans
  exact div_le_div_of_nonneg_right (by exact_mod_cast total) (by norm_num)

private def no5Keep (p : ℕ) : Bool := decide (p ≠ 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem no5SumCertificate :
    accumulate (sieveTerm no5Keep) 2001 = 4121891204 := by decide +kernel

private def no5PrimeSumCoarse : ℚ :=
  ∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2

private theorem no5PrimesCoarse_sum_eq :
    (∑ p ∈ no5PrimesCoarse, (1:ℚ)/(p:ℚ)^2) = no5PrimeSumCoarse := rfl

private theorem no5PrimeSumCoarse_bound :
    no5PrimeSumCoarse + (1:ℚ)/primeCutoff ≤ (413:ℚ) / 1000 := by
  have estimate := sieve_bound no5PrimesCoarse no5Keep (fun p hp => by
    obtain ⟨hpr, pass⟩ := Finset.mem_filter.mp hp
    obtain ⟨hrange, prime⟩ := Finset.mem_filter.mp hpr
    exact ⟨hrange, prime, decide_eq_true pass⟩)
  rw [no5SumCertificate] at estimate
  exact (add_le_add_left estimate ((1:ℚ)/2000) : _).trans (by norm_num [primeCutoff])

lemma sum_Ioc_inv_sq_le_inv (B N : ℕ) (hB : B ≠ 0) :
    (∑ i ∈ Finset.Ioc B N, (1 : ℚ) / (i ^ 2 : ℚ)) ≤ (1 : ℚ) / B := by
  by_cases hBN : B < N
  · have hle : B ≤ N := Nat.le_of_lt hBN
    have hsub := sum_Ioc_inv_sq_le_sub (α := ℚ) (k := B) (n := N) hB hle
    have hnonneg : 0 ≤ (N : ℚ)⁻¹ := by positivity
    have hsub' : (B : ℚ)⁻¹ - (N : ℚ)⁻¹ ≤ (B : ℚ)⁻¹ := sub_le_self _ hnonneg
    simpa [one_div] using hsub.trans hsub'
  · have hIoc : (Finset.Ioc B N) = ∅ := by
      apply Finset.Ioc_eq_empty
      exact not_lt.2 (Nat.le_of_not_gt hBN)
    simp [hIoc, one_div]

def no5PrimesUpTo (N : ℕ) : Finset ℕ :=
  (primesUpTo N).filter (fun p => p ≠ 5)

lemma sq_pred_add_one_lt_sq (N : ℕ) (hN : 100 ≤ N) : (N - 1) * (N - 1) + 1 < N ^ 2 := by
  have h2 : 2 ≤ N := le_trans (by norm_num : 2 ≤ 100) hN
  have h1 : 1 ≤ N := le_trans (by norm_num : 1 ≤ 2) h2
  have hsub : N - 1 + 1 = N := Nat.sub_add_cancel h1
  have hpos : 0 < N - 1 := by omega
  calc (N - 1) * (N - 1) + 1
      < (N - 1) * (N - 1) + 2 * (N - 1) + 1 := by omega
    _ = (N - 1 + 1) * (N - 1 + 1) := by ring
    _ = N * N := by rw [hsub]
    _ = N ^ 2 := by rw [Nat.pow_two]

set_option maxRecDepth 10000 in
lemma sum_no5PrimesUpTo_le (N : ℕ) :
    (∑ p ∈ no5PrimesUpTo N, (1 : ℚ) / (p ^ 2 : ℚ)) ≤ (413 : ℚ) / 1000 := by
  classical
  let f : ℕ → ℚ := fun p => (1 : ℚ) / (p ^ 2 : ℚ)
  have hsubset : no5PrimesUpTo N ⊆ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N := by
    intro p hp
    have hp_mem : p ∈ primesUpTo N := (Finset.mem_filter.1 hp).1
    have hp_cond : p ≠ 5 := (Finset.mem_filter.1 hp).2
    have hp_prime : Nat.Prime p := (Finset.mem_filter.1 hp_mem).2
    have hp_le_N : p ≤ N := by
      have hp_range : p ∈ Finset.range (N + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < N + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    by_cases hp_le_cutoff : p ≤ primeCutoff
    · have hp_mem_cutoff : p ∈ primesUpTo primeCutoff := by
        have hp_lt_cutoff : p < primeCutoff + 1 := Nat.lt_succ_of_le hp_le_cutoff
        simp [primesUpTo, hp_lt_cutoff, hp_prime]
      have : p ∈ no5PrimesCoarse := by
        simp [no5PrimesCoarse, hp_mem_cutoff, hp_cond]
      exact Finset.mem_union.2 (Or.inl this)
    · have hp_gt_cutoff : primeCutoff < p := lt_of_not_ge hp_le_cutoff
      have : p ∈ Finset.Ioc primeCutoff N := by
        simp [Finset.mem_Ioc, hp_gt_cutoff, hp_le_N]
      exact Finset.mem_union.2 (Or.inr this)
  have hdisj : Disjoint no5PrimesCoarse (Finset.Ioc primeCutoff N) := by
    refine Finset.disjoint_left.2 ?_
    intro p hp_coarse hp_Ioc
    have hp_mem : p ∈ primesUpTo primeCutoff := (Finset.mem_filter.1 hp_coarse).1
    have hp_le_cutoff : p ≤ primeCutoff := by
      have hp_range : p ∈ Finset.range (primeCutoff + 1) := (Finset.mem_filter.1 hp_mem).1
      have hp_lt : p < primeCutoff + 1 := Finset.mem_range.1 hp_range
      exact Nat.le_of_lt_succ hp_lt
    have hp_gt_cutoff : primeCutoff < p := (Finset.mem_Ioc.1 hp_Ioc).1
    exact (not_lt_of_ge hp_le_cutoff) hp_gt_cutoff
  have hsum_le_union :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := by
    refine Finset.sum_le_sum_of_subset_of_nonneg hsubset ?_
    intro p _hp _hnot
    positivity
  have hsum_le :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
        no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
    calc
      (∑ p ∈ no5PrimesUpTo N, f p) ≤
          ∑ p ∈ no5PrimesCoarse ∪ Finset.Ioc primeCutoff N, f p := hsum_le_union
      _ = (∑ p ∈ no5PrimesCoarse, f p) + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp [Finset.sum_union hdisj]
      _ = no5PrimeSumCoarse + (∑ i ∈ Finset.Ioc primeCutoff N, f i) := by
          simp only [f, no5PrimesCoarse_sum_eq]
  have htail :
      (∑ i ∈ Finset.Ioc primeCutoff N, f i) ≤ (1 : ℚ) / primeCutoff := by
    simpa [f] using sum_Ioc_inv_sq_le_inv primeCutoff N (by simp [primeCutoff])
  have hsum_le' :
      (∑ p ∈ no5PrimesUpTo N, f p) ≤ no5PrimeSumCoarse + (1 : ℚ) / primeCutoff := by
    exact hsum_le.trans (add_le_add_right htail no5PrimeSumCoarse)
  exact hsum_le'.trans no5PrimeSumCoarse_bound

lemma prime_eq_of_dvd_5 (p : ℕ) (hp : Nat.Prime p) (h : p ∣ 5) : p = 5 := by
  have hp_le5 : p ≤ 5 := Nat.le_of_dvd (by decide : 0 < 5) h
  have hp_ge2 : 2 ≤ p := hp.two_le
  interval_cases p <;> simp_all

lemma coprime_25_pow_two_of_prime_ne5 (p : ℕ) (hp : Nat.Prime p) (hp5 : p ≠ 5) :
    Nat.Coprime 25 (p ^ 2) := by
  have hnot : ¬ p ∣ 25 := by
    intro h
    have hpow : p ∣ 5 ^ 2 := by
      have : (5 ^ 2 : ℕ) = 25 := by rfl
      simpa [this] using h
    have h5 : p ∣ 5 := hp.dvd_of_dvd_pow hpow
    exact hp5 (prime_eq_of_dvd_5 p hp h5)
  simpa [Nat.coprime_comm] using hp.coprime_pow_of_not_dvd (a := 25) (m := 2) hnot

lemma prime_square_exists {n : ℕ} (hn : ¬ Squarefree n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ^ 2 ∣ n := by
  classical
  have hnot : ¬ ∀ p : ℕ, Nat.Prime p → ¬ p * p ∣ n := by
    intro hall
    exact hn ((Nat.squarefree_iff_prime_squarefree).2 hall)
  push Not at hnot
  rcases hnot with ⟨p, hp, hpp⟩
  refine ⟨p, hp, ?_⟩
  simpa [pow_two] using hpp

lemma prime_square_exists_ne5 {n : ℕ} (hn : ¬ Squarefree n) (h25 : ¬ 25 ∣ n) :
    ∃ p : ℕ, Nat.Prime p ∧ p ≠ 5 ∧ p ^ 2 ∣ n := by
  obtain ⟨p, hp, hp2⟩ := prime_square_exists (n := n) hn
  refine ⟨p, hp, ?_, hp2⟩
  intro hp5
  subst hp5
  have : 25 ∣ n := by simpa [pow_two] using hp2
  exact (h25 this).elim

lemma off_count_modEq25_le (N p b t : ℕ) (hp : Nat.Prime p) (hb : ¬ p ∣ b) (hp5 : p ≠ 5) :
    ((Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1)).card ≤
      N / (25 * p ^ 2) + 1 := by
  classical
  have hcop : Nat.Coprime 25 (p ^ 2) := coprime_25_pow_two_of_prime_ne5 p hp hp5
  have hp0 : (p ^ 2 : ℕ) ≠ 0 := pow_ne_zero 2 hp.ne_zero
  let rZ : ZMod (p ^ 2) := -((b : ZMod (p ^ 2))⁻¹)
  let r : ℕ := rZ.val
  have hrZ : (r : ZMod (p ^ 2)) = rZ := by
    have : NeZero (p ^ 2) := ⟨hp0⟩
    simp [r, rZ]
  have hsubset :
      (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ p ^ 2 ∣ b * a + 1) ⊆
        (Finset.range N).filter (fun a => a ≡ t [MOD 25] ∧ a ≡ r [MOD p ^ 2]) := by
    intro a ha
    simp [Finset.mem_filter, Finset.mem_range] at ha ⊢
    refine ⟨ha.1, ha.2.1, ?_⟩
    have hdiv : p ^ 2 ∣ b * a + 1 := ha.2.2
    have hEq : (a : ZMod (p ^ 2)) = -((b : ZMod (p ^ 2))⁻¹) := by
      have : p ^ 2 ∣ b * a + 1 := by simpa [Nat.mul_comm] using hdiv
      exact (dvd_pow_two_mul_add_one_iff_zmod_eq_neg_inv (p := p) (a := b) (b := a) hp hb).1 this
    have : (a : ZMod (p ^ 2)) = (r : ZMod (p ^ 2)) := by
      simpa [rZ, hrZ] using hEq
    exact (ZMod.natCast_eq_natCast_iff a r (p ^ 2)).1 this
  have hcard := Finset.card_le_card hsubset
  exact le_trans hcard (card_filter_modEq_and_modEq_le N 25 (p ^ 2) t r hcop)

lemma prime_le_of_sq_dvd_lt_sq {p N X : ℕ} (hXpos : 0 < X) (hXlt : X < N ^ 2) (hp2 : p ^ 2 ∣ X) : p ≤ N := by
  have hp2_le : p ^ 2 ≤ X := Nat.le_of_dvd hXpos hp2
  have hp2_lt : p ^ 2 < N ^ 2 := lt_of_le_of_lt hp2_le hXlt
  by_contra hp_le
  have hNp : N ≤ p := le_of_lt (Nat.not_le.mp hp_le)
  have hN2le : N ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hNp 2
  exact (not_lt_of_ge hN2le) hp2_lt

lemma sum_div_add_one_le_real (N : ℕ) (P : Finset ℕ) (k : ℕ) :
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hsplit :
      ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := by
    have :
        (∑ p ∈ P, (N / (k * p ^ 2) + 1 : ℕ)) =
          (∑ p ∈ P, (N / (k * p ^ 2) : ℕ)) + P.card := by
      simp [Finset.sum_add_distrib]
    exact_mod_cast this
  have hterm :
      ∀ p ∈ P, ((N / (k * p ^ 2) : ℕ) : ℝ) ≤ (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    intro p hp
    have h := (Nat.cast_div_le (α := ℝ) (m := N) (n := k * p ^ 2))
    simpa [Nat.cast_mul, Nat.cast_pow, mul_assoc, mul_left_comm, mul_comm, div_eq_mul_inv] using h
  have hdiv' :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        ∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2) := by
    exact_mod_cast (Finset.sum_le_sum fun p hp => hterm p hp)
  have hdiv :
      ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) ≤
        (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
    have :
        (∑ p ∈ P, (N : ℝ) / (k * (p : ℝ) ^ 2)) =
          (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) := by
      simp [div_eq_mul_inv, mul_sum, mul_comm]
    exact hdiv'.trans (le_of_eq this)
  have h := add_le_add_right hdiv (P.card : ℝ)
  calc
    ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) =
        ((∑ p ∈ P, (N / (k * p ^ 2) : ℕ) : ℕ) : ℝ) + (P.card : ℝ) := hsplit
    _ ≤ (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
        simpa [add_comm, add_left_comm, add_assoc] using h

lemma sieve_set_card_bound
    (N k : ℕ) (P S : Finset ℕ) (pred : ℕ → ℕ → Prop) [∀ p, DecidablePred (pred p)]
    (hsubset :
      S ⊆ P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n)))
    (hper : ∀ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card ≤ N / (k * p ^ 2) + 1) :
    (S.card : ℝ) ≤
      (N : ℝ) * (∑ p ∈ P, (1 : ℝ) / (k * (p : ℝ) ^ 2)) + (P.card : ℝ) := by
  classical
  have hcard : S.card ≤ (∑ p ∈ P, (N / (k * p ^ 2) + 1)) := by
    calc
      S.card ≤
          ((P.biUnion (fun p => (Finset.range N).filter (fun n => pred p n))).card) :=
        Finset.card_le_card hsubset
      _ ≤ ∑ p ∈ P, ((Finset.range N).filter (fun n => pred p n)).card :=
        Finset.card_biUnion_le
      _ ≤ ∑ p ∈ P, (N / (k * p ^ 2) + 1) := by
          apply Finset.sum_le_sum
          intro p hp
          exact hper p hp
  have hcard_real :
      (S.card : ℝ) ≤ ((∑ p ∈ P, (N / (k * p ^ 2) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hcard
  exact hcard_real.trans (sum_div_add_one_le_real (N := N) (P := P) (k := k))

end Sieve

open Finset

private theorem count_by_theta_refined (N M e : ℕ) (Mpos : 0 < M)
    (hlogM : Real.log (M : ℝ) = e * Real.log 2)
    : e*N.primeCounting ≤ e*M.primeCounting+2*N := by
  let small := N.primesLE.filter (fun q => q ≤ M)
  let large := N.primesLE.filter (fun q => ¬ q ≤ M)
  have partition : small.card + large.card = N.primeCounting := by
    simpa only [small, large, Nat.primesLE_card_eq_primeCounting] using
      (Finset.card_filter_add_card_filter_not (s := N.primesLE) (fun q => q ≤ M))
  have sub : small ⊆ M.primesLE := by
    intro q hq
    obtain ⟨hp,hle⟩ := Finset.mem_filter.mp hq
    exact Nat.mem_primesLE.mpr ⟨hle,(Nat.mem_primesLE.mp hp).2⟩
  have hsmall := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at hsmall
  have filterSub : large ⊆ N.primesLE := Finset.filter_subset _ _
  have lower : (large.card : ℝ) * Real.log M ≤ Chebyshev.theta N := by
    rw [Chebyshev.theta_eq_sum_primesLE_log]
    calc
      (large.card : ℝ) * Real.log M = ∑ _q ∈ large, Real.log M := by simp
      _ ≤ ∑ q ∈ large, Real.log q := by
        apply Finset.sum_le_sum
        intro q hq
        apply Real.log_le_log (by exact_mod_cast Mpos)
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge (Finset.mem_filter.mp hq).2))
      _ ≤ ∑ q ∈ N.primesLE, Real.log q := by
        apply Finset.sum_le_sum_of_subset_of_nonneg filterSub
        intro q hq _
        exact Real.log_nonneg (by exact_mod_cast (Nat.mem_primesLE.mp hq).2.one_lt.le)
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hupper := Chebyshev.theta_le_log4_mul_x (x := (N : ℝ)) (by positivity)
  rw [hlogM] at lower
  rw [hlog4] at hupper
  have hlarge : e * (large.card : ℝ) ≤ 2 * (N : ℝ) := by
    apply (mul_le_mul_iff_left₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mp
    linarith only [lower, hupper]
  have count : (small.card : ℝ) + (large.card : ℝ) = N.primeCounting := by exact_mod_cast partition
  have sm : (small.card : ℝ) ≤ M.primeCounting := by exact_mod_cast hsmall
  exact_mod_cast (show e*(N.primeCounting : ℝ) ≤ e*(M.primeCounting : ℝ)+2*(N : ℝ) by
    nlinarith only [count, hlarge, mul_le_mul_of_nonneg_left sm (show (0:ℝ) ≤ (e:ℝ) by positivity)])

private theorem medium_log_nat_two_pow (n : ℕ) : Real.log ((2^n : ℕ) : ℝ) = n*Real.log 2 := by
  rw [Nat.cast_pow,Real.log_pow]
  norm_num

set_option maxRecDepth 1500 in
theorem prime_count_medium {N : ℕ} (Q : Finset ℕ) (pr : ∀p∈Q,p.Prime)
    (cut : ∀p∈Q,48*p≤N) : 816*Q.card ≤ 2*N + 816*25880 := by
  let X := N/48
  have sub : Q ⊆ X.primesLE := fun p hp => Nat.mem_primesLE.mpr
    ⟨by dsimp [X]; have := cut p hp; omega,pr p hp⟩
  have bound := Finset.card_le_card sub
  rw [Nat.primesLE_card_eq_primeCounting] at bound
  have top := count_by_theta_refined X (2^17) 17 (by decide) (medium_log_nat_two_pow 17)
  have med := count_by_theta_refined (2^17) (2^11) 11 (by decide) (medium_log_nat_two_pow 11)
  have sub' : (2^11).primesLE ⊆ Finset.Icc 1 (2^11) := fun i hi =>
    Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hi).2.pos,(Nat.mem_primesLE.mp hi).1⟩
  have mid := Finset.card_le_card sub'
  rw [Nat.primesLE_card_eq_primeCounting] at mid
  norm_num only [Nat.card_Icc] at mid
  simp only [show (2^17:ℕ) = 131072 by decide,show (2^11:ℕ) = 2048 by decide] at top med mid
  have hX : 48*X≤N := by dsimp [X]; omega
  omega

private theorem root_tag (d p q : ℕ)
    (hp : (d*p^2)%25=2) (hq : (d*q^2)%25=2) (tag : (p%25≤12) = (q%25≤12)) :
    p ≡ q [MOD 25] := by
  have check : ∀ a x y : Fin 25, (a.val*x.val^2)%25=2 → (a.val*y.val^2)%25=2 →
      (x.val≤12) = (y.val≤12) → x=y := by decide +kernel
  let a : Fin 25 := ⟨d%25,Nat.mod_lt _ (by decide)⟩
  let x : Fin 25 := ⟨p%25,Nat.mod_lt _ (by decide)⟩
  let y : Fin 25 := ⟨q%25,Nat.mod_lt _ (by decide)⟩
  have r (z : ℕ) : ((d%25)*(z%25)^2)%25 = (d*z^2)%25 := by
    rw [Nat.mul_mod d, Nat.pow_mod z]
    simp [Nat.mul_mod]
  exact congrArg Fin.val (check a x y ((r p).trans hp) ((r q).trans hq) tag)

/-- Reducing the crossed product modulo 5 forces its complementary divisor to be at least two. -/
private theorem complementClass {d p : ℕ} (h : (d*p^2)%25=2) :
    d%5=2 ∨ d%5=3 := by
  have e : (d*p^2)%5=2 := by omega
  let a : Fin 5 := ⟨d%5,Nat.mod_lt _ (by decide)⟩
  let x : Fin 5 := ⟨p%5,Nat.mod_lt _ (by decide)⟩
  have finite : ∀ a x : Fin 5, (a.val*x.val^2)%5=2 → a.val=2 ∨ a.val=3 := by decide
  apply finite a x
  change ((d%5)*(p%5)^2)%5=2
  have z : ((d%5)*(p%5)^2)%5=(d*p^2)%5 := by
    rw [Nat.mul_mod d,Nat.pow_mod p]
    simp [Nat.mul_mod]
  exact z.trans e

/-- Equal root keys force a gap of at least 25b between the doubled roots. With d ≥ 2
this puts the larger input outside the interval whenever the smaller root exceeds N / 48. -/
private theorem fibre_spacing {b N d x y p q : ℕ} (bp : 0<b) (dp : 2≤d)
    (hy : y<N) (ex : d*p^2=b*x+1) (ey : d*q^2=b*y+1)
    (big : N<48*p) (lt : p<q) (hm : 2*p ≡ 2*q [MOD 25*b]) : False := by
  have gap := hm.add_le_of_lt (by omega : 2*p<2*q)
  let t := q-p
  have expand : q=p+t := by dsimp [t]; omega
  have g : 25*b≤2*t := by omega
  have m := Nat.mul_le_mul_right p g
  have n := Nat.mul_lt_mul_of_pos_right big bp
  have bt : b*N < d*(2*p*t) := by
    nlinarith only [n, Nat.mul_le_mul_left 2 m, Nat.mul_le_mul_right (2*p*t) dp, Nat.zero_le (b*p)]
  have e : b*y = b*x+d*(2*p*t+t^2) := by rw [expand] at ey; nlinarith only [ex,ey]
  have blt := Nat.mul_lt_mul_of_pos_left hy bp
  nlinarith only [e,bt,blt,Nat.zero_le (b*x),Nat.zero_le (d*t^2)]

theorem count_root_fibres {N b : ℕ} (bp : 0 < b) (cop : Nat.Coprime 25 b)
    (S D : Finset ℕ) (p d : ℕ → ℕ)
    (domain : ∀ n∈S,n<N) (eq : ∀ n∈S,d n*(p n)^2=b*n+1)
    (cong : ∀ n∈S,(b*n+1)%25=2) (big : ∀ n∈S,N<48*p n)
    (allowed : ∀ n∈S,d n∈D) :
    S.card ≤ 2*D.card*((b.divisors.filter (fun j => Nat.gcd j (b/j) ∣ 2)).card) := by
  classical
  let anchor (j : ℕ) := if h : ∃ n∈S,d n=j then h.choose else 0
  have spec (n : ℕ) (h : n∈S) : anchor (d n)∈S ∧ d (anchor (d n))=d n := by
    have w : ∃ t∈S,d t=d n := ⟨n,h,rfl⟩
    simpa only [anchor,dif_pos w] using w.choose_spec
  let r (j : ℕ) := p (anchor j)
  let g (n : ℕ) := Int.gcd (b:ℤ) ((p n:ℤ)-(r (d n):ℤ))
  let key (n : ℕ) := (d n, g n, decide ((p n)%25≤12))
  let keys := b.divisors.filter (fun j => Nat.gcd j (b/j) ∣ 2)
  have ez (n : ℕ) (h : n∈S) : (d n:ℤ)*(p n:ℤ)^2=(b:ℤ)*(n:ℤ)+1 := by exact_mod_cast eq n h
  have estimate : S.card ≤ (D.product (keys.product (univ : Finset Bool))).card := by
    apply Finset.card_le_card_of_injOn key
    · intro n hn
      have div : g n∣b := by
        have dg : (g n:ℤ) ∣ (b:ℤ) := Int.gcd_dvd_left ..
        exact_mod_cast dg
      have ea := ez _ (spec n hn).1
      rw [(spec n hn).2] at ea
      exact mem_product.mpr ⟨allowed n hn,mem_product.mpr
        ⟨mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨div,bp.ne'⟩,RootClass.root_key_valid bp ea (ez n hn)⟩,mem_univ _⟩⟩
    · intro x hx y hy h
      have hd : d x=d y := congrArg Prod.fst h
      have hk : g x=g y := congrArg (fun u=>u.2.1) h
      have ht : decide ((p x)%25≤12)=decide ((p y)%25≤12) := congrArg (fun u=>u.2.2) h
      have tag : ((p x)%25≤12) = ((p y)%25≤12) := propext (by simpa using ht)
      have ex := eq x hx
      have ey := eq y hy
      rw [←hd] at ey
      have h25 := root_tag (d x) (p x) (p y) (ex ▸ cong x hx) (ey ▸ cong y hy) tag
      have ea := ez _ (spec x hx).1
      rw [(spec x hx).2] at ea
      have ezy := ez y hy
      rw [←hd] at ezy
      change Int.gcd _ ((p x:ℤ)-(r (d x):ℤ))=Int.gcd _ ((p y:ℤ)-(r (d y):ℤ)) at hk
      rw [←hd] at hk
      have s := RootClass.roots_in_class ea (ez x hx) ezy hk
      have hm : 2*p x ≡ 2*p y [MOD b] := by
        apply Int.natCast_modEq_iff.mp
        rw [Int.modEq_iff_dvd]
        convert! s using 1
        push_cast
        ring
      have both := (Nat.modEq_and_modEq_iff_modEq_mul cop).mp ⟨h25.mul_left 2,hm⟩
      have dp : 2≤d x := by
        have := complementClass (ex ▸ cong x hx : (d x*(p x)^2)%25=2)
        omega
      rcases lt_trichotomy (p x) (p y) with lt|same|gt
      · exact (fibre_spacing bp dp (domain y hy) ex ey (big x hx) lt both).elim
      · rw [same,ey] at ex
        exact Nat.eq_of_mul_eq_mul_left bp (by omega)
      · exact (fibre_spacing bp dp (domain x hx) ey ex (big y hy) gt both.symm).elim
  simpa [keys,Finset.card_product,Nat.mul_comm,Nat.mul_left_comm,Nat.mul_assoc] using estimate

def smallPrimes : Finset ℕ := {2,3,7,11,13,17,19,23}
/-- Bit i records whether i is a nonzero quadratic residue modulo the indicated prime. -/
private def qrBits : ℕ → ℕ
  | 2 => 2
  | 3 => 2
  | 7 => 22
  | 11 => 570
  | 13 => 5658
  | 17 => 107286
  | 19 => 199410
  | 23 => 340830
  | _ => 0

private def qr (q d : ℕ) : Bool := (qrBits q).testBit (d%q)
def admissibleDivs (s : Finset ℕ) := (Finset.range 2305).filter (fun d =>
  (d%5=2 ∨ d%5=3) ∧ ∀ q∈s, qr q d=true)

private theorem qr_ok {q d p : ℕ} (hq : q∈smallPrimes) (h : (d*p^2)%q=1) :
    qr q d=true := by
  have qpos : 0<q := by
    have e : q=2 ∨ q=3 ∨ q=7 ∨ q=11 ∨ q=13 ∨ q=17 ∨ q=19 ∨ q=23 := by simpa [smallPrimes] using hq
    omega
  let a : Fin q := ⟨d%q,Nat.mod_lt _ qpos⟩
  let x : Fin q := ⟨p%q,Nat.mod_lt _ qpos⟩
  have test : ∀ q∈smallPrimes, ∀ a x : Fin q, (a.val*x.val^2)%q=1 → qr q a.val=true := by decide +kernel
  have xx : (a.val*x.val^2)%q=1 := by
    change ((d%q)*(p%q)^2)%q=1
    rw [←h]
    rw [Nat.mul_mod d, Nat.pow_mod p]
    simp [Nat.mul_mod]
  simpa [a,qr] using test q hq a x xx

theorem div_admissible {b n p d : ℕ} (h : d*p^2=b*n+1)
    (res : (b*n+1)%25=2) (bound : d≤2304) : d∈admissibleDivs (b.primeFactors ∩ smallPrimes) := by
  refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),?_,?_⟩
  · exact complementClass (h ▸ res)
  · intro q hq
    obtain ⟨qb,qs⟩ := mem_inter.mp hq
    apply qr_ok qs
    have prime := Nat.prime_of_mem_primeFactors qb
    have dv := dvd_mul_of_dvd_left (Nat.dvd_of_mem_primeFactors qb) n
    rw [h, Nat.add_mod, Nat.mod_eq_zero_of_dvd dv, zero_add, Nat.mod_eq_of_lt prime.one_lt, Nat.mod_eq_of_lt prime.one_lt]

private theorem product_support_bound {b : ℕ} (bp : 0<b) (no5 : ¬5∣b) :
    (∏ q ∈ b.primeFactors ∩ smallPrimes,q) *
        29^(b.primeFactors \ smallPrimes).card ≤ b := by
  let s := b.primeFactors ∩ smallPrimes
  let t := b.primeFactors \ smallPrimes
  have gt (q : ℕ) (hq : q∈t) : 29≤q := by
    obtain ⟨qb,small⟩ := mem_sdiff.mp hq
    have prime := Nat.prime_of_mem_primeFactors qb
    have five : q≠5 := fun e => no5 (e ▸ Nat.dvd_of_mem_primeFactors qb)
    by_contra! low
    interval_cases q <;> norm_num [smallPrimes] at *
  have cmp : 29^t.card ≤ ∏ q∈t,q := by
    rw [←Finset.prod_const]
    exact Finset.prod_le_prod' gt
  have cover : Disjoint s t := Finset.disjoint_left.mpr (by intro q h h'; exact (mem_sdiff.mp h').2 (mem_inter.mp h).2)
  have all : s∪t=b.primeFactors := by ext q; simp [s,t]; tauto
  have div : (∏ q∈b.primeFactors,q) ∣ b := Nat.prod_primeFactors_dvd b
  calc _ ≤ (∏ q∈s,q)*(∏ q∈t,q) := Nat.mul_le_mul_left _ cmp
       _ = _ := by rw [←Finset.prod_union cover,all]
       _ ≤ b := Nat.le_of_dvd bp div

private def listPrimes : List ℕ := [2,3,7,11,13,17,19,23]
private def initial : List ℕ := (List.range 2305).filter fun d => decide (d%5=2 ∨ d%5=3)

/-- Visit both possibilities for each small prime dividing the pivot. At a leaf, c is
the number selected and good contains the divisors passing all their residue tests. -/
private def walk : List ℕ → List ℕ → ℕ → Bool
  | [], good, c => decide (2^c * good.length ≤ 922)
  | q::l, good, c => walk l good c && walk l (good.filter (qr q)) (c+1)

private theorem walk_sound (l good : List ℕ) (c : ℕ) (h : walk l good c=true)
    (s D : Finset ℕ) (sub : ∀ q∈s,q∈l) (domain : ∀ d∈D,d∈good)
    (local_qr : ∀ d∈D,∀ q∈s,qr q d=true) :
    2^(c+s.card)*D.card ≤ 922 := by
  induction l generalizing s good c with
  | nil =>
    have se : s=∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun q hq => by simpa using sub q hq)
    have count : D.card ≤ good.length := (Finset.card_le_card (t:=good.toFinset)
      (fun d hd => List.mem_toFinset.mpr (domain d hd))).trans (List.toFinset_card_le ..)
    simp only [se,card_empty,Nat.add_zero] at *
    have upper : 2^c*good.length ≤ 922 := by simpa [walk] using h
    exact (Nat.mul_le_mul_left _ count).trans upper
  | cons q l ih =>
    simp only [walk,Bool.and_eq_true] at h
    by_cases active : q∈s
    · have sub' (r : ℕ) (hr : r∈s.erase q) : r∈l :=
        (List.mem_cons.mp (sub r (mem_of_mem_erase hr))).resolve_left (ne_of_mem_erase hr)
      have d' (d : ℕ) (hd : d∈D) : d∈good.filter (qr q) :=
        List.mem_filter.mpr ⟨domain d hd,local_qr d hd q active⟩
      have result := ih (good.filter (qr q)) (c+1) h.2 (s.erase q) sub' d'
        (fun d hd r hr => local_qr d hd r (mem_of_mem_erase hr))
      have eq : c+1+(s.erase q).card = c+s.card := by have := card_erase_add_one active; omega
      simpa only [eq] using result
    · exact ih good c h.1 s (fun r hr => (List.mem_cons.mp (sub r hr)).resolve_left (fun e => active (e ▸ hr)))
        domain local_qr

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
private theorem numeric : walk listPrimes initial 0=true := by decide +kernel

private theorem small_table : ∀ s∈smallPrimes.powerset,
    2^s.card * (admissibleDivs s).card ≤ 922 := by
  intro s h
  have a : ∀ q∈s,q∈listPrimes := by
    intro q hq
    simpa [listPrimes,smallPrimes] using (mem_powerset.mp h hq)
  have d : ∀ n∈admissibleDivs s,n∈initial := by
    intro n hn
    obtain ⟨lo,allowed,rest⟩ := mem_filter.mp hn
    exact List.mem_filter.mpr ⟨List.mem_range.mpr (mem_range.mp lo),decide_eq_true allowed⟩
  simpa only [Nat.zero_add] using
    walk_sound listPrimes initial 0 numeric s (admissibleDivs s) a d
      (fun n hn => (mem_filter.mp hn).2.2)

private theorem tail_power (t : ℕ) (ht : 6 ≤ t) :
    1300 * (4*922*2^t) ≤ 29^t := by
  induction t, ht using Nat.le_induction with
  | base => decide
  | succ t ht ih =>
    calc
      1300*(4*922*2^(t+1)) = (1300*(4*922*2^t))*2 := by ring
      _ ≤ 29^t*2 := Nat.mul_le_mul_right _ ih
      _ ≤ 29^(t+1) := by rw [pow_succ]; exact Nat.mul_le_mul_left _ (by decide)

/-- The small-prime table accounts for a factor at most 922. Each other prime divisor
is at least 29, so its contribution of two root choices is absorbed by the size of b. -/
private theorem divisor_weight {b N : ℕ} (largeN : 160000000 ≤ N)
    (bp : 0<b) (no5 : ¬5∣b) (bn : b≤N) :
    1300 * (4*2^b.primeFactors.card*(admissibleDivs (b.primeFactors ∩ smallPrimes)).card) ≤ N := by
  let s := b.primeFactors ∩ smallPrimes
  let t := b.primeFactors \ smallPrimes
  have table := small_table s (mem_powerset.mpr inter_subset_right)
  have pos : 0< ∏ q∈s,q := Finset.prod_pos (fun q h =>
    (Nat.prime_of_mem_primeFactors (mem_inter.mp h).1).pos)
  have tail : 29^t.card ≤ b := calc
    29^t.card = 1 * 29^t.card := by simp
    _ ≤ (∏ q∈s,q)*29^t.card := Nat.mul_le_mul_right _ pos
    _ ≤ b := product_support_bound bp no5
  have size : t.card+s.card=b.primeFactors.card := card_sdiff_add_card_inter _ _
  have weight : 4*2^b.primeFactors.card*(admissibleDivs s).card ≤ 4*922*2^t.card := by
    rw [←size, pow_add]
    nlinarith only [Nat.mul_le_mul_left (4*2^t.card) table]
  apply (Nat.mul_le_mul_left 1300 weight).trans
  by_cases few : t.card ≤ 5
  · have h := Nat.pow_le_pow_right (by decide : 0<2) few
    norm_num at h
    omega
  · exact (tail_power _ (by omega)).trans (tail.trans bn)

private theorem large_primes {N b : ℕ} (big : 160000000 ≤ N) (bN : b < N)
    (no5 : ¬5∣b) (S : Finset ℕ) (mods : ∀ n∈S, (b*n+1)%25=2)
    (choosePrime : ∀ n∈S, n<N ∧ ∃ p : ℕ, N<48*p ∧ p^2 ∣ b*n+1) :
    1300*S.card ≤ N := by
  classical
  let p (n : ℕ) := if h : n ∈ S then ((choosePrime n h).2).choose else 1
  let d (n : ℕ) := (b*n+1)/(p n)^2
  have info (n : ℕ) (hn : n ∈ S) : N < 48*p n ∧ (p n)^2 ∣ b*n+1 := by
    simpa only [p,dif_pos hn] using ((choosePrime n hn).2).choose_spec
  have eq (n : ℕ) (hn : n ∈ S) : d n*(p n)^2 = b*n+1 := Nat.div_mul_cancel (info n hn).2
  have bp : 0 < b := Nat.pos_of_ne_zero (fun h => no5 (h ▸ dvd_zero 5))
  have bound (n : ℕ) (hn : n∈S) : b*n+1 ≤ b*N := by
    have h := Nat.mul_le_mul_left b (show n+1 ≤ N from (choosePrime n hn).1)
    rw [Nat.mul_add,Nat.mul_one] at h
    omega
  have link (n : ℕ) (hn : n∈S) (c : ℕ) (lc : N<c*p n) : d n*N<c^2*b := by
    have positive : 0<d n := by
      by_contra! dz
      have e := eq n hn
      rw [show d n=0 by omega,zero_mul] at e
      omega
    have rr := Nat.mul_lt_mul_of_pos_left (Nat.pow_lt_pow_left lc (by decide : 2≠0)) positive
    have bd := Nat.mul_le_mul_left (c^2) (bound n hn)
    have scaled := congrArg (c^2*·) (eq n hn)
    have cmp : (d n*N)*N < (c^2*b)*N := by nlinarith only [rr,bd,scaled]
    exact Nat.lt_of_mul_lt_mul_right cmp
  let D := admissibleDivs (b.primeFactors ∩ smallPrimes)
  have da (n : ℕ) (hn : n∈S) : d n∈D := by
    apply div_admissible (eq n hn) (mods n hn)
    have cmp := link n hn 48 (info n hn).1
    have l : d n*N < 2304*N := cmp.trans_le (Nat.mul_le_mul_left 2304 bN.le)
    exact Nat.le_of_lt (Nat.lt_of_mul_lt_mul_right l)
  have cop : Nat.Coprime 25 b := (Nat.prime_five.coprime_iff_not_dvd.mpr no5).pow_left 2
  have cnt := count_root_fibres bp cop S D p d (fun n h => (choosePrime n h).1) eq mods
    (fun n h => (info n h).1) da
  have key := Unitary.count_unitary_keys b bp
  have count : S.card ≤ 4*2^b.primeFactors.card*D.card := calc
       _ ≤ _ := cnt
       _ ≤ (2*D.card)*(2*2^b.primeFactors.card) := Nat.mul_le_mul_left _ key
       _ = 4*2^b.primeFactors.card*D.card := by ring
  exact (Nat.mul_le_mul_left 1300 count).trans (divisor_weight big bp no5 bN.le)

open Sieve

private theorem crt_prime_sum (N : ℕ) (P : Finset ℕ) (no5 : P ⊆ no5PrimesUpTo N) :
    (∑ p ∈ P, (1:ℝ)/(25*(p:ℝ)^2)) ≤ 413/25000 := by
  have h : (∑ p ∈ P,(1:ℚ)/(p:ℚ)^2) ≤ 413/1000 :=
    (Finset.sum_le_sum_of_subset_of_nonneg no5 (fun i _ _ => by positivity)).trans
      (sum_no5PrimesUpTo_le N)
  have cast := (Rat.cast_le (K:=ℝ)).mpr h
  simp only [Rat.cast_sum,Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_natCast,
    Rat.cast_ofNat] at cast
  have f (p : ℕ) : (1:ℝ)/(25*(p:ℝ)^2) = (1/25) * (1/(p:ℝ)^2) := by ring
  simp only [f,←Finset.mul_sum]
  linarith only [cast]

/-- Combine the reciprocal-square mass, the rounding error for the small primes, and
the complementary-divisor bound for the large primes. The two units of slack handle
the endpoint when the two residue classes are added. -/
private theorem one_class {N b r : ℕ} (big : 160000000 ≤ N) (bn : b<N)
    (no5b : ¬5∣b) (prod : (b*r+1)%25=2)
    (S : Finset ℕ) (inRange : S ⊆ range N) (res : ∀ n∈S,n ≡ r [MOD 25])
    (bad : ∀ n∈S, ¬Squarefree (b*n+1)) :
    50*S.card+2 ≤ N := by
  classical
  let P := (no5PrimesUpTo N).filter (fun p => ¬p∣b)
  let Q := P.filter (fun p => 48*p≤N)
  let R := P.filter (fun p => N<48*p)
  let B (p : ℕ) := (range N).filter (fun n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
  have no5 : P ⊆ no5PrimesUpTo N := Finset.filter_subset ..
  have prime {p : ℕ} (h : p ∈ P) : p.Prime :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp (no5 h)).1).2
  have residue {n : ℕ} (hr : n ≡ r [MOD 25]) : (b*n+1)%25=2 := by
    have e := (hr.mul_left b).add_right 1
    exact Eq.trans (α:=ℕ) e prod
  have cover : S ⊆ Q.biUnion B ∪ R.biUnion B := by
    intro n hn
    have h25 : ¬25∣b*n+1 := fun h =>
      (by decide : (0:ℕ) ≠ 2) ((Nat.mod_eq_zero_of_dvd h).symm.trans (residue (res n hn)))
    obtain ⟨p,hp,p5,pdv⟩ := prime_square_exists_ne5 (bad n hn) h25
    have nN := Finset.mem_range.mp (inRange hn)
    have pred := Nat.mul_le_mul (Nat.le_pred_of_lt bn) (Nat.le_pred_of_lt nN)
    have le := prime_le_of_sq_dvd_lt_sq (Nat.succ_pos _) ((Nat.add_le_add_right pred 1).trans_lt
      (sq_pred_add_one_lt_sq N (by omega))) pdv
    have pnd : ¬p∣b := by
      intro h
      exact hp.not_dvd_one ((Nat.dvd_add_right (dvd_mul_of_dvd_left h n)).mp
        (Nat.dvd_of_pow_dvd (by decide : 1 ≤ 2) pdv))
    have mem : p ∈ P := by
      simp [P,no5PrimesUpTo,primesUpTo,hp,Nat.lt_succ_of_le le,p5,pnd]
    have nb : n ∈ B p := Finset.mem_filter.mpr ⟨inRange hn,res n hn,pdv⟩
    by_cases h : 48*p ≤ N
    · exact mem_union_left _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,h⟩,nb⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨p,mem_filter.mpr ⟨mem,Nat.lt_of_not_ge h⟩,nb⟩)
  have cards : S.card ≤ (Q.biUnion B).card + (R.biUnion B).card :=
    (card_le_card cover).trans (card_union_le ..)
  have sub : Q ⊆ P := Finset.filter_subset ..
  have lc := prime_count_medium Q (fun _ h => prime (sub h)) (fun _ h => (mem_filter.mp h).2)
  have hc := large_primes big bn no5b (R.biUnion B) (by
    intro n hn
    obtain ⟨p,_,mem⟩ := Finset.mem_biUnion.mp hn
    exact residue (Finset.mem_filter.mp mem).2.1) (by
    intro n hn
    obtain ⟨p,hp,nb⟩ := Finset.mem_biUnion.mp hn
    obtain ⟨nN,pdv⟩ := Finset.mem_filter.mp nb
    exact ⟨Finset.mem_range.mp nN,p,(mem_filter.mp hp).2,pdv.2⟩)
  have first := sieve_set_card_bound N 25 Q (Q.biUnion B) (fun p n => n ≡ r [MOD 25] ∧ p^2∣b*n+1)
    Subset.rfl (fun p hp => off_count_modEq25_le N p b r (prime (sub hp))
      (mem_filter.mp (sub hp)).2 (mem_filter.mp (no5 (sub hp))).2)
  have est := crt_prime_sum N Q (sub.trans no5)
  have weight := mul_le_mul_of_nonneg_left est (show 0 ≤ (N:ℝ) by positivity)
  have countR : (S.card:ℝ) ≤ ((Q.biUnion B).card:ℝ) + ((R.biUnion B).card:ℝ) := by exact_mod_cast cards
  have lcr : 816*(Q.card:ℝ) ≤ 2*(N:ℝ)+816*25880 := by exact_mod_cast lc
  have hcr : 1300 * ((R.biUnion B).card:ℝ) ≤ N := by exact_mod_cast hc
  have bigR : (160000000:ℝ) ≤ N := by exact_mod_cast big
  exact_mod_cast (show 50*(S.card:ℝ)+2 ≤ N by
    norm_num only [Nat.cast_ofNat] at first
    linarith only [first,weight,countR,lcr,hcr,bigR])

open scoped Classical in
private theorem opposite_count {N b r : ℕ} (big : 160000000 ≤ N) (bn : b≤N)
    (no5 : ¬5∣b) (prod : (b*r+1)%25=2) (hr : r<25) :
    50*((Icc 1 N).filter (fun a => a%25=r ∧ ¬Squarefree (a*b+1))).card+2 ≤ N+1 := by
  classical
  let S := (Icc 1 N).filter (fun a => a%25=r ∧ ¬Squarefree (a*b+1))
  have res (n : ℕ) (hn : n∈S) : n ≡ r [MOD 25] := by
    change n%25=r%25
    rw [Nat.mod_eq_of_lt hr]
    exact (mem_filter.mp hn).2.1
  apply one_class (N:=N+1) (by omega) (by omega) no5 prod S
  · intro n hn
    exact mem_range.mpr (Nat.lt_succ_of_le (mem_Icc.mp (mem_filter.mp hn).1).2)
  · exact res
  · intro n hn
    simpa only [Nat.mul_comm b n] using (mem_filter.mp hn).2.2

open scoped Classical in
theorem crossed {N b b' : ℕ} (big : 160000000 ≤ N) (hb : b ≤ N) (h7 : b%25=7)
    (hb' : b' ≤ N) (h18 : b'%25=18) :
    ((Icc 1 N).filter (fun a => a%25=18 ∧ ¬Squarefree (a*b+1))).card +
      ((Icc 1 N).filter (fun a => a%25=7 ∧ ¬Squarefree (a*b'+1))).card ≤
      ((Icc 1 N).filter (fun a => a%25=7)).card := by
  classical
  have pr {p r s : ℕ} (h : p%25=s) : (p*r+1)%25 = (s*r+1)%25 :=
    ((show p ≡ s [MOD 25] from by change p%25=s%25; rw [← h, Nat.mod_mod]).mul_right r).add_right 1
  have first := opposite_count (r:=18) big hb (by omega)
    ((pr (r:=18) h7).trans (by decide)) (by decide)
  have second := opposite_count (r:=7) big hb' (by omega)
    ((pr (r:=7) h18).trans (by decide)) (by decide)
  have eq : (Icc 1 N).filter (fun a => a%25=7) = (range (N+1)).filter (fun a => a%25=7) := by
    ext a
    simp only [mem_filter,mem_Icc,mem_range]
    omega
  rw [eq, card_range_filter_mod25_eq 7 (by decide)]
  omega

end CrossedResidue

theorem OMA.solution : OMA.R_Erdos848_erdos_848_R1_H2_R1_H2_R1.H1 := by
  intro N lower _
  dsimp only
  intro b b' hb h7 hb' h18
  exact CrossedResidue.crossed lower
    (Finset.mem_Icc.mp hb.1).2 h7 (Finset.mem_Icc.mp hb'.1).2 h18
