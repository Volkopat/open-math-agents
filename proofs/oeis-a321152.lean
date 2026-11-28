import OMAStatements.S_oeis_a321152
import Mathlib

/-! # The exact set of practical complements, OEIS A321152

Frank M Jackson proposed this list in 2018. We use the practical-number
criterion of Stewart and Sierpiński, a sieve with one forbidden residue per
prime, dyadic primorial bounds, and finite divisor-subsum certificates.
https://oeis.org/A321152
-/

namespace PracticalComplements

/-- The subset-sum definition of Nat.IsPractical, written with Mathlib Finsets. -/
def practical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → ∃ s : Finset ℕ, s ⊆ n.divisors ∧ m = ∑ i ∈ s, i

def qualifies (n : ℕ) : Prop :=
  2 ≤ n ∧ ∀ s : ℕ, n ≤ 2*s → s < n → practical s → practical (n-s)

def known : List ℕ := [2,3,4,5,6,8,10,12,14,16,18,20,24,36,48,60,72,84,96,120]

end PracticalComplements

/-! Subset sums and the practical component, adapted from the proof in
the contributor's reduction of Coleman's A017666 (open-math-agents PR 5541).
The prime-power argument is the Stewart–Sierpiński characterization. -/

namespace PracticalComplements
open ArithmeticFunction
open scoped ArithmeticFunction.sigma

def subsetSums (A : Set ℕ) : Set ℕ :=
  {m | ∃ s : Finset ℕ, (s : Set ℕ) ⊆ A ∧ m = ∑ i ∈ s, i}

def positivePractical (n : ℕ) : Prop := 0 < n ∧ practical n

theorem practical_one : practical 1 := by
  intro m hm
  interval_cases m
  · exact ⟨∅, by simp, by simp⟩
  · exact ⟨{1}, by simp, by simp⟩


lemma covered_digit_split {m a b p : ℕ} (hp : 0 < p) (hg : p ≤ a + 1)
    (hm : m ≤ a + p * b) : ∃ x ≤ a, ∃ y ≤ b, m = x + p * y := by
  by_cases h : m / p ≤ b
  · have hr := Nat.mod_lt m hp
    have he := Nat.div_add_mod m p
    exact ⟨m % p, by omega, m / p, h, by omega⟩
  · have hle := Nat.mul_le_mul_left p (show b ≤ m / p by omega)
    have he := Nat.mul_div_le m p
    exact ⟨m - p * b, by omega, b, le_rfl, by omega⟩

lemma covered_union_image (A B : Finset ℕ) {p : ℕ} (hp : 0 < p)
    (hd : Disjoint A (B.image (p * ·))) (hg : p ≤ (∑ a ∈ A, a) + 1)
    (hA : ∀ x, x ≤ ∑ a ∈ A, a → x ∈ subsetSums (A : Set ℕ))
    (hB : ∀ x, x ≤ ∑ b ∈ B, b → x ∈ subsetSums (B : Set ℕ)) :
    ∀ m, m ≤ ∑ d ∈ A ∪ (B.image (p * ·)), d →
      m ∈ subsetSums ((A ∪ (B.image (p * ·)) : Finset ℕ) : Set ℕ) := by
  have hsum (s : Finset ℕ) : (∑ d ∈ s.image (p * ·), d) = p * ∑ i ∈ s, i := by
    rw [Finset.sum_image, Finset.mul_sum]
    intro u hu v hv he
    exact Nat.mul_left_cancel hp he
  intro m hm
  rw [Finset.sum_union hd, hsum] at hm
  obtain ⟨x, hx, y, hy, he⟩ := covered_digit_split hp hg hm
  obtain ⟨s, hs, es⟩ := hA x hx
  obtain ⟨t, ht, et⟩ := hB y hy
  have hs' : s ⊆ A := hs
  have ht' : t.image (p * ·) ⊆ B.image (p * ·) := Finset.image_subset_image ht
  refine ⟨s ∪ t.image (p * ·), ?_, ?_⟩
  · exact Finset.union_subset_union hs' ht'
  · rw [Finset.sum_union (hd.mono hs' ht'), hsum, ← es, ← et]
    exact he

lemma practical_prime_layer {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (e : ℕ) :
    (c * p ^ (e + 1)).divisors =
      c.divisors ∪ ((c * p ^ e).divisors.image (p * ·)) := by
  have hn : c * p ^ (e + 1) ≠ 0 := Nat.mul_ne_zero hc.ne' (pow_ne_zero _ hp.ne_zero)
  have hn' : c * p ^ e ≠ 0 := Nat.mul_ne_zero hc.ne' (pow_ne_zero _ hp.ne_zero)
  have he : c * p ^ (e + 1) = p * (c * p ^ e) := by rw [pow_succ]; ac_rfl
  ext d
  simp only [Finset.mem_union, Nat.mem_divisors, hn, hn', hc.ne', ne_eq,
    not_false_eq_true, and_true, Finset.mem_image]
  constructor
  · intro h
    by_cases hpd : p ∣ d
    · obtain ⟨u, rfl⟩ := hpd
      rw [he] at h
      exact Or.inr ⟨u, Nat.dvd_of_mul_dvd_mul_left hp.pos h, rfl⟩
    · exact Or.inl (((hp.coprime_iff_not_dvd.mpr hpd).symm.pow_right _).dvd_of_dvd_mul_right h)
  · rintro (h | ⟨u, hu, rfl⟩)
    · exact dvd_mul_of_dvd_left h _
    · rw [he]
      exact Nat.mul_dvd_mul_left p hu

lemma cover_mul_prime_pow {c p : ℕ} (hc : 0 < c) (hp : p.Prime) (hcp : c.Coprime p)
    (hgap : p ≤ (∑ d ∈ c.divisors, d) + 1)
    (hcover : ∀ m, m ≤ ∑ d ∈ c.divisors, d → m ∈ subsetSums (c.divisors : Set ℕ))
    (e : ℕ) : ∀ m, m ≤ ∑ d ∈ (c * p ^ e).divisors, d →
      m ∈ subsetSums ((c * p ^ e).divisors : Set ℕ) := by
  induction e with
  | zero => simpa using hcover
  | succ e ih =>
    rw [practical_prime_layer hc hp e]
    apply covered_union_image _ _ hp.pos _ hgap hcover ih
    apply Finset.disjoint_left.mpr
    intro d hd hdp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hdp
    exact (hp.coprime_iff_not_dvd.mp hcp.symm)
      ((dvd_mul_right p t).trans (Nat.mem_divisors.mp hd).1)

theorem whole_le_sigma {c : ℕ} (hc : 0 < c) : c ≤ σ 1 c := by
  rw [ArithmeticFunction.sigma_one_apply]
  exact Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) (Nat.mem_divisors.mpr ⟨dvd_rfl, hc.ne'⟩)

theorem coprime_to_tail {c b t : ℕ} (ht : 0 < t) (hbound : t ≤ σ 1 c + 1)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p) : t.Coprime b := by
  by_contra h
  obtain ⟨p, hp, hpt, hpb⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
  exact (not_lt_of_ge ((Nat.le_of_dvd ht hpt).trans hbound)) (hrough p hp hpb)

theorem practical_divisor_dvd_prefix {c b d : ℕ} (hc : 0 < c)
    (hd : positivePractical d) (hdiv : d ∣ c * b)
    (hrough : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p) : d ∣ c := by
  have small (t : ℕ) (ht : 0 < t) (hsize : t ≤ σ 1 c + 1) (htd : t ∣ d) : t ∣ c :=
    (coprime_to_tail ht hsize hrough).dvd_of_dvd_mul_right (htd.trans hdiv)
  by_contra h
  have hsize : σ 1 c + 1 ≤ d := by
    by_contra! hdsmall
    exact h (small d hd.1 (by omega) dvd_rfl)
  obtain ⟨S, hS, hsum⟩ := hd.2 _ hsize
  have hsub : S ⊆ c.divisors := by
    intro x hx
    have hxdiv := Nat.mem_divisors.mp (hS hx)
    have hxle : x ≤ ∑ i ∈ S, i := Finset.single_le_sum (f := fun i : ℕ => i) (fun _ _ => Nat.zero_le _) hx
    exact Nat.mem_divisors.mpr ⟨small x (Nat.pos_of_dvd_of_pos hxdiv.1 hd.1) (hsum ▸ hxle) hxdiv.1, hc.ne'⟩
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub (f := fun i : ℕ => i) (by intros; omega)
  rw [← ArithmeticFunction.sigma_one_apply] at hle
  omega

theorem component_from_cover
    {n : ℕ} (hn : 0 < n) (hnot : ¬ positivePractical n)
    (b c : ℕ) (hcb : n = c * b) (hcop : c.Coprime b)
    (hcover : ∀ m, m ≤ ∑ d ∈ c.divisors, d → m ∈ subsetSums (c.divisors : Set ℕ)) :
    ∃ u v : ℕ, n = u * v ∧ 1 < v ∧ u.Coprime v ∧
      ∀ p : ℕ, p.Prime → p ∣ v → σ 1 u + 1 < p := by
  induction b using Nat.strong_induction_on generalizing c with
  | h b ih =>
    have hc : 0 < c := by by_contra! hz; simp_all
    have hb : 0 < b := by by_contra! hz; simp_all
    have hb1 : b ≠ 1 := by
      rintro rfl
      simp only [mul_one] at hcb
      subst n
      apply hnot
      refine ⟨hc, fun m hm => hcover m (hm.trans ?_)⟩
      simpa only [ArithmeticFunction.sigma_one_apply] using whole_le_sigma hc
    by_cases hr : ∀ p : ℕ, p.Prime → p ∣ b → σ 1 c + 1 < p
    · exact ⟨c, b, hcb, by omega, hcop, hr⟩
    push Not at hr
    obtain ⟨p, hp, hpb, hl⟩ := hr
    obtain ⟨e, t, hpt, hbt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hb.ne' p hp.ne_one
    have he : e ≠ 0 := by rintro rfl; simp_all
    have ht : 0 < t := by by_contra! hz; simp_all
    have hpow : 1 < p ^ e := one_lt_pow₀ hp.one_lt he
    have htb : t < b := by rw [hbt]; simpa using Nat.mul_lt_mul_of_pos_right hpow ht
    have htt : t ∣ b := by rw [hbt]; exact dvd_mul_left _ _
    have hcp := Nat.Coprime.coprime_dvd_right hpb hcop
    have hct := Nat.Coprime.coprime_dvd_right htt hcop
    have hptcop := hp.coprime_iff_not_dvd.mpr hpt
    apply ih t htb (c * p ^ e)
    · rw [hcb, hbt, Nat.mul_assoc]
    · exact hct.mul_left (hptcop.pow_left e)
    · exact cover_mul_prime_pow hc hp hcp (by simpa only [ArithmeticFunction.sigma_one_apply] using hl) hcover e

theorem has_practical_component {n : ℕ} (hn : 0 < n) (hnot : ¬ positivePractical n) :
    ∃ u v : ℕ, n = u * v ∧ 1 < v ∧ u.Coprime v ∧
      ∀ p : ℕ, p.Prime → p ∣ v → σ 1 u + 1 < p := by
  apply component_from_cover hn hnot n 1 (by simp) (by simp)
  intro m hm
  apply practical_one m
  simpa using hm

end PracticalComplements

namespace PracticalComplements

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

private def fullCover (c : ℕ) : Prop :=
  ∀ m, m ≤ ∑ d ∈ c.divisors, d → m ∈ subsetSums (c.divisors : Set ℕ)

private theorem practical_of_cover {c : ℕ} (hc : 0 < c) (h : fullCover c) : practical c := by
  intro m hm
  exact h m (hm.trans (by simpa only [sigma_one_apply] using whole_le_sigma hc))

theorem practical_mul_small {m j : ℕ} (hm : practical m) (hm0 : 0 < m)
    (hj : 0 < j) (hjbound : j ≤ m) : practical (m*j) := by
  by_contra h
  obtain ⟨c,b,hcb,hbig,hcop,hrough⟩ := has_practical_component (Nat.mul_pos hm0 hj) (fun hh => h hh.2)
  have hc : 0 < c := by by_contra! hz; simp_all
  have hmc : m ∣ c := practical_divisor_dvd_prefix hc ⟨hm0,hm⟩
    (hcb ▸ dvd_mul_right m j) hrough
  have hjs : j ≤ σ 1 c+1 := by
    have := Nat.le_of_dvd hc hmc
    have := whole_le_sigma hc
    omega
  have hcop' : (m*j).Coprime b :=
    (Nat.Coprime.coprime_dvd_left hmc hcop).mul_left (coprime_to_tail hj hjs hrough)
  have hd : b ∣ m*j := hcb.symm ▸ dvd_mul_left b c
  have e := hcop'.gcd_eq_one
  rw [Nat.gcd_eq_right hd] at e
  omega

private theorem cover_two_pow (b : ℕ) : fullCover (2^b) := by
  have h1 : fullCover 1 := by
    intro m hm
    exact practical_one m (by simpa using hm)
  simpa only [fullCover, one_mul] using cover_mul_prime_pow (c := 1) (by decide) Nat.prime_two
    (by simp) (by simp) h1 b

theorem sigma_two_pow (b : ℕ) : σ 1 (2^b)+1 = 2*(2^b) := by
  rw [sigma_one_apply_prime_pow Nat.prime_two]
  simpa [pow_succ, Nat.mul_comm] using geom_sum_mul_add (1:ℕ) (b+1)

theorem practical_base (b a p : ℕ) (hp : p.Prime) (hsize : p ≤ 2*(2^b)) :
    practical (2^b*p^a) := by
  apply practical_of_cover (Nat.mul_pos (pow_pos (by decide) _) (pow_pos hp.pos _))
  by_cases h : p = 2
  · subst p
    simpa only [← pow_add] using cover_two_pow (b+a)
  · have hcop : (2^b).Coprime p := (Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm h) |>.pow_left b
    exact cover_mul_prime_pow (pow_pos (by decide) _) hp hcop
      (by rwa [← sigma_one_apply, sigma_two_pow]) (cover_two_pow b) a

theorem not_practical_rough {t b : ℕ} (ht : 2*(2^b) < t) (h2 : ¬2^(b+1)∣t)
    (hOdd : ∀ r, r.Prime → r≠2 → r≤2*(2^b) → ¬r∣t) : ¬practical t := by
  intro hp
  have ht0 : 0 < t := by omega
  obtain ⟨e,u,hu,heu⟩ := Nat.exists_eq_pow_mul_and_not_dvd ht0.ne' 2 (by decide)
  have heb : e ≤ b := by
    by_contra! h
    exact h2 ((pow_dvd_pow 2 h).trans (heu ▸ dvd_mul_right (2^e) u))
  have hpow : 2^e ≤ 2^b := Nat.pow_le_pow_right (by decide) heb
  have hs : ∀ r, r.Prime → r∣u → σ 1 (2^e)+1 < r := by
    intro r hr hd
    rw [sigma_two_pow]
    by_contra! h
    have hne : r ≠ 2 := fun he => hu (he ▸ hd)
    apply hOdd r hr hne (by omega)
    exact hd.trans (heu ▸ dvd_mul_left u (2^e))
  have hdiv : t ∣ 2^e := practical_divisor_dvd_prefix (pow_pos (by decide) _) ⟨ht0,hp⟩
    (dvd_of_eq heu) hs
  have := Nat.le_of_dvd (pow_pos (by decide) _) hdiv
  omega

end PracticalComplements

namespace PracticalComplements

theorem term_iff_qualifies (n : ℕ) : OMA.S_oeis_a321152.isTerm n ↔ qualifies n := by
  constructor
  · rintro ⟨⟨s, hs⟩, hall⟩
    obtain ⟨_, hslt, hpos, _⟩ := hs
    refine ⟨by omega, ?_⟩
    intro t ht htlt hpr
    exact (hall t ⟨ht, htlt, by omega, hpr⟩).2
  · rintro ⟨hn, hall⟩
    refine ⟨?_, ?_⟩
    · let b := (n-1).log2
      have hle : 2^b ≤ n-1 := Nat.log2_self_le (by omega)
      have hlt : n-1 < 2^b*2 := by
        simpa only [pow_succ] using (Nat.lt_log2_self (n := n-1))
      have hp : 0 < 2^b := pow_pos (by decide) _
      refine ⟨2^b, by omega, by omega, hp, ?_⟩
      change practical (2^b)
      simpa only [pow_zero, mul_one] using practical_base b 0 2 Nat.prime_two (by omega)
    · rintro s ⟨hs, hslt, _, hpr⟩
      exact ⟨by omega, hall s hs hslt hpr⟩

end PracticalComplements

namespace PracticalComplements
open Finset

/-- Avoid one arbitrary forbidden residue for each prime, in every full window. -/
def goodWindow (S : Finset ℕ) (H : ℕ) : Prop :=
  ∀ (a : ℕ → ℕ) (start : ℕ), ∃ j : ℕ, start ≤ j ∧ j < start+H ∧
    ∀ r ∈ S, ¬ j ≡ a r [MOD r]

def tailPrimes (S : Finset ℕ) (W : ℕ) := S.filter (fun r => ¬r ∣ W)

private def hit (start W u r a : ℕ) : Finset ℕ :=
  (range u).filter (fun i => start + W*i ≡ a [MOD r])

private theorem hit_bound {start W u r a : ℕ} (h : r.Coprime W) :
    (hit start W u r a).card ≤ u/r+1 := by
  have bound : (hit start W u r a).card ≤ (range (u/r+1)).card := by
    apply card_le_card_of_injOn (fun i : ℕ => i/r)
    · intro j hj
      have hj' : j < u ∧ start+W*j ≡ a [MOD r] := by simpa [hit] using hj
      exact mem_range.mpr (Nat.lt_succ_of_le (Nat.div_le_div_right hj'.1.le))
    · intro i hi j hj he
      have hi' : i < u ∧ start+W*i ≡ a [MOD r] := by simpa [hit] using hi
      have hj' : j < u ∧ start+W*j ≡ a [MOD r] := by simpa [hit] using hj
      have hmod : i ≡ j [MOD r] := Nat.ModEq.cancel_left_of_coprime h
        ((Nat.ModEq.refl start).add_left_cancel (hi'.2.trans hj'.2.symm))
      have hi'' := Nat.div_add_mod i r
      have hj'' := Nat.div_add_mod j r
      change i/r=j/r at he
      change i%r=j%r at hmod
      rw [he,hmod] at hi''
      omega
  simpa using bound

/-- A single class modulo W avoids all its prime divisors. A union bound
    in that class handles the remaining primes. -/
theorem wheel_window (S : Finset ℕ) (W u : ℕ) (hW : 0 < W)
    (hS : ∀ r ∈ S, r.Prime)
    (hbudget : (∑ r ∈ tailPrimes S W, (u/r+1)) < u) :
    goodWindow S (W*u) := by
  classical
  intro a start
  let B := S.filter (fun r => r ∣ W)
  have Bprime {r : ℕ} (hr : r ∈ B) : r.Prime := hS r (mem_filter.mp hr).1
  let hne := fun r (hr : r ∈ B) => (Bprime hr).ne_zero
  have hpairs : Set.Pairwise (B : Set ℕ) (fun i j : ℕ => i.Coprime j) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (Bprime hi) (Bprime hj)).mpr hij
  let f := fun r => a r + 1 + r*(start+1) - start
  let k := Nat.chineseRemainderOfFinset f id B hne hpairs
  have hprod : (∏ r ∈ B, r) ∣ W := Finset.prod_primes_dvd W
    (fun r hr => Nat.prime_iff.mp (Bprime hr)) (fun r hr => (mem_filter.mp hr).2)
  have hk : (k:ℕ) < W :=
    (Nat.chineseRemainderOfFinset_lt_prod f id hne hpairs).trans_le (Nat.le_of_dvd hW hprod)
  let L := start+(k:ℕ)
  let T := tailPrimes S W
  have hgood : ∃ i ∈ range u, ∀ r ∈ T, ¬L+W*i ≡ a r [MOD r] := by
    by_contra! h
    have hsub : range u ⊆ T.biUnion (fun r => hit L W u r (a r)) := by
      intro i hi
      obtain ⟨r,hr,he⟩ := h i hi
      exact mem_biUnion.mpr ⟨r,hr,mem_filter.mpr ⟨hi,he⟩⟩
    have hc : u ≤ ∑ r ∈ T, (u/r+1) := calc
      u = (range u).card := (card_range _).symm
      _ ≤ _ := card_le_card hsub
      _ ≤ _ := card_biUnion_le
      _ ≤ _ := sum_le_sum (fun r hr => hit_bound
        ((hS r (mem_filter.mp hr).1).coprime_iff_not_dvd.mpr (mem_filter.mp hr).2))
    exact (not_lt_of_ge hc) hbudget
  obtain ⟨i,hi,hgood⟩ := hgood
  have hi' := mem_range.mp hi
  refine ⟨L+W*i, by dsimp [L]; omega, ?_, ?_⟩
  · have := Nat.mul_le_mul_left W (show i+1 ≤ u by omega)
    dsimp [L]
    nlinarith
  · intro r hr he
    by_cases hd : r ∣ W
    · have hb : r ∈ B := mem_filter.mpr ⟨hr,hd⟩
      have hrp := (hS r hr).two_le
      have hf : start+f r = a r+1+r*(start+1) := by
        have := Nat.mul_le_mul_right (start+1) (by omega : 1 ≤ r)
        dsimp [f]; omega
      have h1 := (k.property r hb).add_left start
      change L ≡ start + f r [MOD r] at h1
      rw [hf] at h1
      have h2 : L+W*i ≡ a r + 1 [MOD r] := by
        have hW0 := (dvd_mul_of_dvd_left hd i).modEq_zero_nat
        have hr0 := (dvd_mul_right r (start+1)).modEq_zero_nat
        simpa using (h1.add hW0).trans ((Nat.ModEq.refl (a r+1)).add hr0)
      have ha := h2.symm.trans he
      have hd1 : r ∣ 1 := by
        simpa using (Nat.modEq_iff_dvd' (by omega : a r ≤ a r+1)).mp ha.symm
      exact (not_le_of_gt (by omega : 1 < r)) (Nat.le_of_dvd (by decide) hd1)
    · exact hgood r (mem_filter.mpr ⟨hr,hd⟩) he

end PracticalComplements

namespace PracticalComplements
open Finset

def sievePrimes (C p : ℕ) : Finset ℕ := (Nat.primesLE (2*C)).erase p

theorem prime_of_mem_sieve {C p r : ℕ} (h : r ∈ sievePrimes C p) : r.Prime :=
  (Nat.mem_primesLE.mp (mem_erase.mp h).2).2

def casesList : List (ℕ × ℕ) :=
  [(3,2),(5,8),(7,10),(11,34),(13,36),(17,150),(19,150),(23,156)]

private def wheelData : ℕ → ℕ × ℕ
  | 3 => (2,1)
  | 5 => (2,4)
  | 7 => (2,5)
  | 11 => (2,17)
  | 13 => (2,18)
  | 17 => (6,25)
  | 19 => (6,25)
  | 23 => (6,26)
  | 29 => (6,27)
  | 31 => (6,27)
  | 37 => (6,103)
  | 41 => (6,105)
  | 43 => (6,106)
  | 47 => (6,107)
  | 53 => (6,109)
  | 59 => (6,110)
  | 61 => (6,111)
  | 67 => (30,142)
  | 71 => (30,143)
  | 73 => (30,143)
  | 79 => (30,144)
  | 83 => (30,144)
  | 89 => (30,145)
  | 97 => (30,146)
  | 101 => (30,146)
  | 103 => (30,146)
  | 107 => (30,146)
  | 109 => (30,147)
  | 113 => (30,147)
  | 127 => (30,148)
  | _ => (1,1)

set_option maxHeartbeats 0 in
set_option maxRecDepth 12000 in
private theorem checked : ∀ i : Fin 128, i.val.Prime → i.val ≠ 2 →
    let p := i.val
    let C := 2^(Nat.log 2 p)
    let W := (wheelData p).1
    let u := (wheelData p).2
    0 < W ∧ (∑ r ∈ tailPrimes (sievePrimes C p) W, (u/r+1)) < u ∧
      ((p,W*u) ∈ casesList ∨ 4*p^2*(W*u+3)^2 ≤ primorial (p-1)) := by
  decide +kernel

theorem small_window {p : ℕ} (hp : p.Prime) (hne : p ≠ 2) (hlt : p < 128) :
    ∃ H : ℕ, goodWindow (sievePrimes (2^(Nat.log 2 p)) p) H ∧
      ((p,H) ∈ casesList ∨ 4*p^2*(H+3)^2 ≤ primorial (p-1)) := by
  have h := checked ⟨p,hlt⟩ hp hne
  exact ⟨_,wheel_window _ _ _ h.1 (fun _ ht => prime_of_mem_sieve ht) h.2.1, h.2.2⟩

theorem big_window (C p : ℕ) (hC : 0 < C)
    (hrecip : (∑ r ∈ (Nat.primesLE (2*C)).filter (C/8 < ·), (1 / (r:ℚ))) ≤ 15/16) :
    goodWindow (sievePrimes C p) (primorial (C/8)*(64*C+1)) := by
  let W := primorial (C/8)
  let S := sievePrimes C p
  let T := tailPrimes S W
  let u := 64*C+1
  have hsub : T ⊆ (Nat.primesLE (2*C)).filter (C/8 < ·) := by
    intro r hr
    rcases mem_filter.mp hr with ⟨hrs,hn⟩
    have hs := (mem_erase.mp hrs).2
    exact mem_filter.mpr ⟨hs,lt_of_not_ge (fun he => hn ((Nat.mem_primesLE.mp hs).2.dvd_primorial_iff.mpr he))⟩
  have hTR : (∑ r ∈ T, (1/(r:ℚ))) ≤ 15/16 :=
    (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans hrecip
  have hsC : T ⊆ Icc 1 (2*C) := by
    intro r hr
    have hp := Nat.mem_primesLE.mp (mem_filter.mp (hsub hr)).1
    exact mem_Icc.mpr ⟨hp.2.pos,hp.1⟩
  have htC : T.card ≤ 2*C := by simpa using card_le_card hsC
  apply wheel_window _ _ _ (primorial_pos _) (fun _ ht => prime_of_mem_sieve ht)
  change (∑ r ∈ T, (u/r+1)) < u
  have term : ∀ r ∈ T, ((u/r:ℕ):ℚ) ≤ (u:ℚ)*(1/r) := by
    intro r hr
    obtain ⟨_,hp⟩ := Nat.mem_primesLE.mp (mem_filter.mp (hsub hr)).1
    rw [mul_one_div,le_div_iff₀ (by exact_mod_cast hp.pos)]
    exact_mod_cast Nat.div_mul_le_self u r
  have hh : (∑ r ∈ T, ((u/r:ℕ):ℚ)) ≤ (u:ℚ)*(15/16) := calc
    _ ≤ ∑ r ∈ T, (u:ℚ)*(1/r) := sum_le_sum term
    _ = (u:ℚ)*(∑ r ∈ T, 1/(r:ℚ)) := (mul_sum ..).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left hTR (by positivity)
  have hc : (T.card:ℚ) ≤ 2*C := by exact_mod_cast htC
  have hcast : (∑ r ∈ T, (((u/r:ℕ):ℚ)+1)) < u := by
    simp only [sum_add_distrib,sum_const,nsmul_eq_mul,mul_one]
    dsimp [u] at hh ⊢
    push_cast at hh ⊢
    linarith
  exact_mod_cast hcast

end PracticalComplements

namespace PracticalComplements
open Finset

private theorem choose_scale {n C p : ℕ} (hC : 0 < C) (hp : 1 < p) (hn : C^2 < n) :
    ∃ a : ℕ, 0 < a ∧ n ≤ (C*p^a)^2 ∧ (C*p^a)^2 < p^2*n := by
  have hex : ∃ a : ℕ, n ≤ (C*p^a)^2 := by
    refine ⟨n,?_⟩
    have ht : n < p^n := Nat.lt_pow_self hp
    have hc : p^n ≤ C*p^n := Nat.le_mul_of_pos_left _ hC
    nlinarith
  let a := Nat.find hex
  have ha : n ≤ (C*p^a)^2 := Nat.find_spec hex
  cases he : a with
  | zero => simp [he] at ha; omega
  | succ d =>
    have hbefore : (C*p^d)^2 < n := by
      apply lt_of_not_ge
      intro h
      have hv := Nat.find_min' hex h
      change a ≤ d at hv
      omega
    refine ⟨d+1,by omega,he ▸ ha,?_⟩
    calc (C*p^(d+1))^2 = p^2*(C*p^d)^2 := by rw [pow_succ]; ring
         _ < _ := Nat.mul_lt_mul_of_pos_left hbefore (by positivity)

private theorem odd_small {n : ℕ} (hn : qualifies n) (ho : Odd n) : n < 36 := by
  by_contra! high
  obtain ⟨a,ha,hl,hh⟩ := choose_scale (C:=1) (p:=2) (n:=n) (by decide) (by decide) (by omega)
  simp only [one_mul] at hl hh
  let P := 2^a
  have hP : 0 < P := pow_pos (by decide) _
  have ht : 2*P+4 < n := by
    by_contra! he
    change P^2 < 2^2*n at hh
    have hg : n^2 ≤ (2*P+4)^2 := Nat.pow_le_pow_left he 2
    nlinarith [sq_nonneg (P:ℤ), Nat.mul_le_mul_left (n-36) high,
      Nat.mul_le_mul_left n high]
  let j := n/(2*P)+1
  have hdown : n < j*(2*P) := (Nat.div_lt_iff_lt_mul (by positivity)).mp (Nat.lt_succ_self _)
  have hup : (j-1)*(2*P) ≤ n := by simpa [j] using Nat.div_mul_le_self n (2*P)
  have hj' : j = (j-1)+1 := by dsimp [j]
  have hroom : P*j+2 < n := by nlinarith only [hup,ht,congrArg (P*·) hj']
  have hle : j ≤ P := by
    by_contra! h
    have hv := Nat.mul_lt_mul_of_pos_left h hP
    change n ≤ P^2 at hl
    nlinarith
  have hp : practical P := by
    simpa [P] using (practical_base a 0 2 Nat.prime_two (Nat.mul_le_mul_left 2 hP))
  have h2 := hn.2 (P*j) (by nlinarith only [hdown]) (by omega)
    (practical_mul_small hp hP (Nat.succ_pos _) hle)
  apply (not_practical_rough (t:=n-P*j) (b:=0) (by simp; omega) ?_ ?_) h2
  · change ¬2 ∣ n-P*j
    have hd : 2 ∣ P*j := dvd_mul_of_dvd_left (dvd_pow_self 2 ha.ne') _
    intro h
    have hd' := dvd_add h hd
    rw [Nat.sub_add_cancel (by omega : P*j ≤ n)] at hd'
    exact (Nat.not_even_iff_odd.mpr ho) (even_iff_two_dvd.mpr hd')
  · intro r hr hne hr2
    simp only [pow_zero,mul_one] at hr2
    have := hr.two_le
    omega

private noncomputable def forbidden (n P C r : ℕ) : ℕ := by
  classical
  exact if r=2 then n/C else
    if h : ∃ i : ℕ, P*i ≡ n [MOD r] then Nat.find h else 0

private theorem exclude_remainder {n p b a j : ℕ} (hp : p.Prime) (hne : p ≠ 2)
    (ha : 0 < a) (hn : ¬p ∣ n)
    (hfit : (2^b*p^a)*j ≤ n) (hroom : 2*(2^b) < n-(2^b*p^a)*j)
    (hgood : ∀ r ∈ sievePrimes (2^b) p, ¬j ≡ forbidden n (2^b*p^a) (2^b) r [MOD r]) :
    ¬practical (n-(2^b*p^a)*j) := by
  let C := 2^b
  let P := C*p^a
  have hC : 0 < C := pow_pos (by decide) _
  have hpodd : Odd p := hp.odd_of_ne_two hne
  apply not_practical_rough hroom
  · intro hd
    obtain ⟨w,hw⟩ := hd
    have he : n=C*(p^a*j+2*w) := by
      rw [pow_succ] at hw
      dsimp [C]
      have := Nat.sub_add_cancel hfit
      nlinarith only [hw,this]
    have hr2 : 2 ∈ sievePrimes C p := Finset.mem_erase.mpr ⟨hne.symm,
      Nat.mem_primesLE.mpr ⟨by omega,Nat.prime_two⟩⟩
    apply hgood 2 hr2
    simp only [forbidden,if_true]
    have hnC : n/C=p^a*j+2*w := by rw [he,Nat.mul_div_cancel_left _ hC]
    change j ≡ n/C [MOD 2]
    rw [hnC]
    have ho : p^a % 2 = 1 := Nat.odd_iff.mp (hpodd.pow)
    simp [Nat.ModEq,Nat.add_mod,Nat.mul_mod,ho]
  · intro r hr hr2 hrle hrt
    by_cases he : r=p
    · subst r
      have hd : p ∣ (2^b*p^a)*j := dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (dvd_pow_self p ha.ne') _) _
      exact hn (Nat.sub_add_cancel hfit ▸ dvd_add hrt hd)
    · have hmem : r ∈ sievePrimes C p := mem_erase.mpr ⟨he,Nat.mem_primesLE.mpr ⟨hrle,hr⟩⟩
      have hactual : P*j ≡ n [MOD r] := (Nat.modEq_iff_dvd' hfit).mpr hrt
      have hex : ∃ i : ℕ, P*i ≡ n [MOD r] := ⟨j,hactual⟩
      have hc : r.Coprime P := ((Nat.coprime_primes hr Nat.prime_two).mpr hr2).pow_right b |>.mul_right
        (((Nat.coprime_primes hr hp).mpr he).pow_right a)
      apply hgood r hmem
      change j ≡ forbidden n P C r [MOD r]
      simp only [forbidden,if_neg hr2,dif_pos hex]
      exact Nat.ModEq.cancel_left_of_coprime hc (hactual.trans (Nat.find_spec hex).symm)

theorem window_cap {n p b H : ℕ} (hn : qualifies n) (hp : p.Prime) (hne : p ≠ 2)
    (hmiss : ¬p ∣ n) (hlo : 2^b ≤ p) (hhi : p ≤ 2*(2^b))
    (hwin : goodWindow (sievePrimes (2^b) p) H) :
    n < 4*p^2*(H+3)^2 := by
  by_contra! high
  let C := 2^b
  have hC : 0 < C := pow_pos (by decide) _
  have hbefore : C^2 < n := by
    have ht := Nat.pow_le_pow_left hlo 2
    change C^2 ≤ p^2 at ht
    have hpos := pow_pos (by omega : 0 < H+3) 2
    nlinarith [Nat.mul_le_mul_left (4*p^2) hpos,hp.two_le]
  obtain ⟨a,ha,hPlo,hPhi⟩ := choose_scale hC hp.one_lt hbefore
  let P := C*p^a
  have hP : 0 < P := Nat.mul_pos hC (pow_pos hp.pos _)
  have hPC : C ≤ P := Nat.le_mul_of_pos_right _ (pow_pos hp.pos _)
  change n ≤ P^2 at hPlo
  change P^2 < p^2*n at hPhi
  have hroom : 2*P*(H+3) < n := by
    have hsmall := Nat.mul_lt_mul_of_pos_right hPhi (by positivity : 0 < 4*(H+3)^2)
    have hlarge := Nat.mul_le_mul_right n high
    exact Nat.mul_self_lt_mul_self_iff.mp (by nlinarith only [hsmall,hlarge])
  let start := n/(2*P)+1
  obtain ⟨j,hjlo,hjhi,hgood⟩ := hwin (forbidden n P C) start
  have hdown : n < start*(2*P) := (Nat.div_lt_iff_lt_mul (by positivity)).mp (Nat.lt_succ_self _)
  have hup := Nat.div_mul_le_self n (2*P)
  have hlow := Nat.mul_le_mul_right (2*P) hjlo
  have hj : j ≤ n/(2*P)+H := by dsimp [start] at hjhi; omega
  have hhigh := Nat.mul_le_mul_right (2*P) hj
  have hremain : P*j + 2*C < n := by nlinarith only [hhigh,hroom,hup,hPC]
  have hjle : j ≤ P := by
    by_contra! hh
    have := Nat.mul_lt_mul_of_pos_left hh hP
    nlinarith
  have hs := hn.2 (P*j) (by nlinarith only [hlow,hdown]) (by omega)
    (practical_mul_small (practical_base b a p hp hhi) hP (lt_of_lt_of_le (Nat.succ_pos _) hjlo) hjle)
  exact exclude_remainder hp hne ha hmiss (by omega : P*j ≤ n) (by omega : 2*C < n-P*j) hgood hs

theorem odd_cap {n : ℕ} (hn : qualifies n) (ho : Odd n) : n < 36 := odd_small hn ho

end PracticalComplements

namespace PracticalComplements

open Finset

private theorem lcm_estimate (n : ℕ) (hn : 0<n) :
    Nat.lcmUpto n ≤ n^n.sqrt * primorial n := by
  let S := n.primesLE
  rw [Nat.lcmUpto_eq_prod_pow_log, ← Finset.prod_filter_mul_prod_filter_not S (· ≤ n.sqrt)]
  apply mul_le_mul' 
  · calc
      _ ≤ ∏ _p ∈ S.filter (· ≤ n.sqrt), n :=
        Finset.prod_le_prod' (fun p _ => Nat.pow_log_le_self p hn.ne')
      _ ≤ n^n.sqrt := by
        rw [Finset.prod_const]
        apply Nat.pow_le_pow_right hn
        have hs : S.filter (· ≤ n.sqrt) ⊆ Finset.Icc 1 n.sqrt := by
          intro p hp
          exact Finset.mem_Icc.mpr ⟨(Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2.one_lt.le,
            (Finset.mem_filter.mp hp).2⟩
        simpa using Finset.card_le_card hs
  · calc
      _ ≤ ∏ p ∈ S.filter (fun p => ¬p ≤ n.sqrt), p := by
        apply Finset.prod_le_prod'
        intro p hp
        have pp := (Nat.mem_primesLE.mp (Finset.mem_filter.mp hp).1).2
        have he : p.log n ≤ 1 := Nat.lt_succ_iff.mp
          ((Nat.log_lt_iff_lt_pow pp.one_lt hn.ne').mpr
            (Nat.sqrt_lt'.mp (not_le.mp (Finset.mem_filter.mp hp).2)))
        simpa using Nat.pow_le_pow_right pp.pos he
      _ ≤ primorial n := by
        rw [primorial_eq_prod_primesLE]
        apply Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        intro p hp _
        exact (Nat.mem_primesLE.mp hp).2.one_lt.le

private theorem primes_estimate (n : ℕ) :
    10*(n.primesLE.card) ≤ 2*n + 10240 := by
  let S := n.primesLE
  let T := S.filter (1024 ≤ ·)
  have ht : (1024:ℕ)^T.card ≤ primorial n := calc
    _ = ∏ _p ∈ T, 1024 := by simp
    _ ≤ ∏ p ∈ T, p := Finset.prod_le_prod' (fun p hp => (Finset.mem_filter.mp hp).2)
    _ ≤ primorial n := by
      rw [primorial_eq_prod_primesLE]
      exact Finset.prod_le_prod_of_subset_of_one_le' (Finset.filter_subset _ _)
        (fun p hp _ => (Nat.mem_primesLE.mp hp).2.one_lt.le)
  have hpow : (2:ℕ)^(10*T.card) ≤ 2^(2*n) := by
    simpa only [pow_mul,show (2:ℕ)^10=1024 by decide,show (2:ℕ)^2=4 by decide]
      using ht.trans (primorial_le_four_pow n)
  have hl : 10*T.card ≤ 2*n := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp hpow
  have hrem : (S.filter (fun p => ¬1024≤p)).card ≤ 1024 := by
    calc _ ≤ (Finset.range 1024).card := Finset.card_le_card (fun p hp =>
             Finset.mem_range.mpr (not_le.mp (Finset.mem_filter.mp hp).2))
         _ = _ := Finset.card_range _
  have hc := Finset.card_filter_add_card_filter_not (s:=S) (1024 ≤ ·)
  change T.card + _ = n.primesLE.card at hc
  omega

private theorem exp_room (b : ℕ) (hb : 16 ≤ b) : 8*b ≤ 2^(b/2) := by
  induction b using Nat.strong_induction_on with
  | h b ih =>
    by_cases h : b≤17
    · interval_cases b <;> decide
    · have h1 := ih (b-2) (by omega) (by omega)
      rw [show b/2=(b-2)/2+1 by omega,pow_succ]
      omega

private theorem root_room (b : ℕ) (hb : 16≤b) : 8*(b*((2^b : ℕ).sqrt)) ≤ 2^b := by
  have h1 := exp_room b hb
  have h2 : ((2^b : ℕ).sqrt) ≤ 2^((b+1)/2) := by
    have ha : (2:ℕ)^b ≤ (2^((b+1)/2))^2 := by
      rw [←pow_mul]
      exact Nat.pow_le_pow_right (by decide) (by omega)
    simpa using Nat.sqrt_le_sqrt ha
  have := Nat.mul_le_mul h1 h2
  rw [←pow_add,show b/2+(b+1)/2=b by omega] at this
  simpa [Nat.mul_assoc] using this

theorem large_dyadic (b : ℕ) (hb : 16≤b) :
    let C := 2^b; let k := (Nat.primesLE (2*C)).card-1; let H:=(k+1)*2^k+1
    4*(2*C)^2*(H+3)^2 < primorial C := by
  let C := 2^b
  let k := (Nat.primesLE (2*C)).card-1
  change 4*(2*C)^2*((k+1)*2^k+1+3)^2 < primorial C
  have hC : 65536≤C := Nat.pow_le_pow_right (by decide : 0<2) hb
  have hk : 10*k≤4*C+10240 := by
    have := primes_estimate (2*C)
    dsimp [k]
    omega
  have hbC : 256*b ≤ C := by
    have h8 := exp_room b hb
    have hthirty : 32 ≤ (2:ℕ)^((b+1)/2) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 5≤(b+1)/2)
    have hh := Nat.mul_le_mul h8 hthirty
    rw [←pow_add,show b/2+(b+1)/2=b by omega] at hh
    dsimp [C]
    omega
  have hroot : 8*(b*C.sqrt) ≤ C := root_room b hb
  have he : (2*k + 4*b+10) + (b+1+b*C.sqrt) < C := by omega
  have hplus : C+1 ≤ 2^(b+1) := by dsimp [C] at *; rw [pow_succ]; omega
  have hcost : (C+1)*C^C.sqrt ≤ 2^(b+1+b*C.sqrt) := by
    rw [pow_add,pow_mul]
    exact Nat.mul_le_mul_right _ hplus
  have hbound : 2^C ≤ 2^(b+1+b*C.sqrt)*primorial C := calc
    _ ≤ (C+1)*Nat.lcmUpto C := Chebyshev.two_pow_le_mul_lcmUpto _
    _ ≤ (C+1)*(C^C.sqrt*primorial C) := Nat.mul_le_mul_left _ (lcm_estimate _ (by omega))
    _ ≤ _ := by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hcost
  have hfinal : 2^(2*k+4*b+10) < primorial C := by
    by_contra! hn
    have ht := Nat.mul_le_mul_left (2^(b+1+b*C.sqrt)) hn
    rw [←pow_add] at ht
    have ht' := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (hbound.trans ht)
    omega
  apply lt_of_le_of_lt _ hfinal
  have hk1 : k+1+4 ≤ 2^(b+1) := by rw [pow_succ]; change k+1+4≤C*2; omega
  have ha : (k+1)*2^k+1+3 ≤ 2^(b+1+k) := by
    rw [pow_add]
    have hp : 0 < (2:ℕ)^k := by positivity
    nlinarith only [Nat.mul_le_mul_right (2^k) hk1,hp]
  calc
    _ ≤ 4*(2*C)^2*(2^(b+1+k))^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha 2)
    _ = 2^(2+2*(b+1)+2*(b+1+k)) := by
      dsimp [C]
      rw [show 2+2*(b+1)+2*(b+1+k)=2+(b+1)*2+(b+1+k)*2 by omega]
      simp only [pow_add,pow_mul,pow_one]
      ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

private theorem wheel_estimate (b : ℕ)
    (he : let C := 2^b; 4*(C/8)+4*b+20+(b+1+b*C.sqrt)<C) :
    let C := 2^b; let H := primorial (C/8)*(32*(2*C)+1)
    4*(2*C)^2*(H+3)^2 < primorial C := by
  let C := 2^b
  let e := 2*(C/8)+b+8
  let H := primorial (C/8)*(32*(2*C)+1)
  have hp : 0<C := pow_pos (by decide) _
  have hs : C+1 ≤ 2^(b+1) := by rw [pow_succ]; change C+1≤C*2; omega
  have hcost : (C+1)*C^C.sqrt ≤ 2^(b+1+b*C.sqrt) := by
    rw [pow_add,pow_mul]
    exact Nat.mul_le_mul_right _ hs
  have hbound : 2^C ≤ 2^(b+1+b*C.sqrt)*primorial C := calc
    _ ≤ (C+1)*Nat.lcmUpto C := Chebyshev.two_pow_le_mul_lcmUpto _
    _ ≤ (C+1)*(C^C.sqrt*primorial C) := Nat.mul_le_mul_left _ (lcm_estimate _ hp)
    _ ≤ _ := by rw [←Nat.mul_assoc]; exact Nat.mul_le_mul_right _ hcost
  have hfinal : 2^(4*(C/8)+4*b+20) < primorial C := by
    by_contra! hn
    have ht := Nat.mul_le_mul_left (2^(b+1+b*C.sqrt)) hn
    rw [←pow_add] at ht
    have ht' := (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp (hbound.trans ht)
    change 4*(C/8)+4*b+20+(b+1+b*C.sqrt)<C at he
    omega
  have hw : primorial (C/8) ≤ 2^(2*(C/8)) := by
    rw [pow_mul]; exact primorial_le_four_pow _
  have h64 : 32*(2*C)+1 ≤ 2^(b+7) := by
    rw [pow_add]; change 32*(2*C)+1 ≤ C*128; omega
  have hab : H ≤ 2^(2*(C/8)+b+7) := by
    rw [show 2*(C/8)+b+7=2*(C/8)+(b+7) by omega,pow_add]
    exact Nat.mul_le_mul hw h64
  have hx : H+3 ≤ 2^e := by
    have ht : 4≤(2:ℕ)^(2*(C/8)+b+7) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 2≤2*(C/8)+b+7)
    dsimp [e]
    rw [show 2*(C/8)+b+8=2*(C/8)+b+7+1 by omega,pow_succ]
    omega
  apply lt_of_le_of_lt _ hfinal
  calc
    _ ≤ 4*(2*C)^2*(2^e)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hx 2)
    _ = 2^(2+(b+1)*2+e*2) := by
      dsimp [C]; simp only [pow_add,pow_mul,pow_one]; ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide : 0<2) (by dsimp [e]; omega)

theorem large_wheel (b : ℕ) (hb : 7≤b) :
    let C := 2^b; let H := primorial (C/8)*(32*(2*C)+1)
    4*(2*C)^2*(H+3)^2 < primorial C := by
  by_cases h : b<10
  · interval_cases b <;> decide +kernel
  apply wheel_estimate
  by_cases hsmall : b<16
  · interval_cases b <;> decide +kernel
  let C := 2^b
  have hC : 65536≤C := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 16≤b)
  have hr := root_room b (by omega)
  change 8*(b*C.sqrt)≤C at hr
  have hu := exp_room b (by omega)
  have hd : 32 ≤ (2:ℕ)^((b+1)/2) := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 5≤(b+1)/2)
  have hh := Nat.mul_le_mul hu hd
  rw [←pow_add,show b/2+(b+1)/2=b by omega] at hh
  change (8*b)*32≤C at hh
  change 4*(C/8)+4*b+20+(b+1+b*C.sqrt)<C
  omega

end PracticalComplements

namespace PracticalComplements
open Finset

private def wheelHit (n : ℕ) : ℕ := if n.Coprime 210 then 1 else 0
private def wheelCount (n : ℕ) := ∑ i ∈ range n, wheelHit i
private def residues (n : ℕ) := (range n).filter (fun i => i.Coprime 210)
private def band (a b : ℕ) := b.primesLE.filter (a < ·)
private def mass (a b : ℕ) : ℚ := ∑ p ∈ band a b, 1/(p:ℚ)
private def score (a : ℕ) := 8*(band a (2*a)).card+4*(band (2*a) (4*a)).card+
  2*(band (4*a) (8*a)).card+(band (8*a) (16*a)).card

private theorem size_residues (n : ℕ) : (residues n).card=wheelCount n := by
  simp only [residues,wheelCount,wheelHit,Finset.card_filter]

private def countInitial : ℕ → ℕ
  | 0 => 0
  | n+1 => countInitial n + wheelHit n

private theorem prefix_eq_initial (n : ℕ) : wheelCount n=countInitial n := by
  induction n with
  | zero => simp [wheelCount,countInitial]
  | succ n ih => simpa [wheelCount,Finset.sum_range_succ,countInitial] using congrArg (·+wheelHit n) ih
private theorem prefix_block (n : ℕ) : wheelCount (210+n)=48+wheelCount n := by
  have hh : wheelCount 210=48 := by rw [prefix_eq_initial]; decide +kernel
  change (∑ i ∈ range (210+n), wheelHit i)=48+wheelCount n
  rw [sum_range_add]
  change wheelCount 210 + _ = 48 + wheelCount n
  rw [hh]
  apply congrArg (48+·)
  apply Finset.sum_congr rfl
  intro i _
  simp [wheelHit,Nat.coprime_comm, Nat.add_comm]

private theorem prefix_mul (q r : ℕ) : wheelCount (210*q+r)=48*q+wheelCount r := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show 210*(q+1)+r=210+(210*q+r) by omega,prefix_block,ih]
    omega

private theorem discrepancy (n : ℕ) :
    48*n ≤ 210*wheelCount n+318 ∧ 210*wheelCount n ≤ 48*n+270 := by
  have h : ∀ i : Fin 210, 48*i.val ≤ 210*countInitial i.val+318 ∧
      210*countInitial i.val ≤ 48*i.val+270 := by decide +kernel
  have hr := h ⟨n%210, Nat.mod_lt n (by decide)⟩
  change 48*(n%210) ≤ 210*countInitial (n%210)+318 ∧
    210*countInitial (n%210) ≤ 48*(n%210)+270 at hr
  have e := prefix_mul (n/210) (n%210)
  rw [Nat.div_add_mod, prefix_eq_initial (n%210)] at e
  omega

private theorem interval_count (a : ℕ) (ha : 7≤a) :
    wheelCount (a+1)+(band a (2*a)).card≤wheelCount (2*a+1) := by
  let s := residues (a+1)
  let t := band a (2*a)
  have hd : Disjoint s t := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have := mem_range.mp (mem_filter.mp hp).1
    have := (mem_filter.mp hq).2
    omega
  have hsub : s ∪ t ⊆ residues (2*a+1) := by
    intro p hp
    rcases mem_union.mp hp with h|h
    · obtain ⟨hl,hc⟩ := mem_filter.mp h
      exact mem_filter.mpr ⟨mem_range.mpr (by have := mem_range.mp hl; omega),hc⟩
    · obtain ⟨hm,hl⟩ := mem_filter.mp h
      obtain ⟨hu,pp⟩ := Nat.mem_primesLE.mp hm
      refine mem_filter.mpr ⟨mem_range.mpr (by omega),pp.coprime_iff_not_dvd.mpr ?_⟩
      intro hh
      have hf := pp.mem_primeFactors hh (by decide : (210:ℕ)≠0)
      have hv : (210:ℕ).primeFactors={2,3,5,7} := by decide +kernel
      simp [hv] at hf
      omega
  have hh := card_le_card hsub
  rw [card_union_of_disjoint hd] at hh
  change (residues (a+1)).card+(band a (2*a)).card≤(residues (2*a+1)).card at hh
  simpa only [size_residues] using hh

private theorem card_band (a : ℕ) (ha : 7≤a) : 210*(band a (2*a)).card ≤ 48*a+588 := by
  have hh := interval_count a ha
  have h1 := discrepancy (a+1)
  have h2 := discrepancy (2*a+1)
  omega

private def evalCount (n : ℕ) := 48*(n/210)+countInitial (n%210)

private theorem evalCount_eq (n : ℕ) : wheelCount n=evalCount n := by
  have h := prefix_mul (n/210) (n%210)
  rw [Nat.div_add_mod, prefix_eq_initial (n%210)] at h
  exact h

private def allowance (a : ℕ) := evalCount (2*a+1)-evalCount (a+1)

private theorem allowance_le (a : ℕ) (ha : 7≤a) : (band a (2*a)).card ≤ allowance a := by
  have hh := interval_count a ha
  simp only [evalCount_eq] at hh
  dsimp [allowance]
  omega

private theorem small_scores (a : ℕ) (ha : 7≤a) :
    score a≤8*allowance a+4*allowance (2*a)+2*allowance (4*a)+allowance (8*a) := by
  have h0 := allowance_le a ha
  have h1 := allowance_le (2*a) (by omega)
  have h2 := allowance_le (4*a) (by omega)
  have h3 := allowance_le (8*a) (by omega)
  rw [show 2*(2*a)=4*a by omega] at h1
  rw [show 2*(4*a)=8*a by omega] at h2
  rw [show 2*(8*a)=16*a by omega] at h3
  dsimp [score]
  omega

private theorem score_bound (a : ℕ) (ha : 228≤a) : 16*score a ≤15*(8*a) := by
  have h0 := card_band a (by omega)
  have h1 := card_band (2*a) (by omega)
  have h2 := card_band (4*a) (by omega)
  have h3 := card_band (8*a) (by omega)
  rw [show 2*(2*a)=4*a by omega] at h1
  rw [show 2*(4*a)=8*a by omega] at h2
  rw [show 2*(8*a)=16*a by omega] at h3
  dsimp [score]
  omega

private theorem mass_split (a b c : ℕ) (hab : a≤b) (hbc : b≤c) :
    mass a c=mass a b+mass b c := by
  have hs : band a c=band a b ∪ band b c := by
    ext p
    by_cases hp : p.Prime
    · simp [band,Nat.mem_primesLE,hp]
      omega
    · simp [band,Nat.mem_primesLE,hp]
  have hd : Disjoint (band a b) (band b c) := by
    apply Finset.disjoint_left.mpr
    intro p hp hq
    have := (Nat.mem_primesLE.mp (mem_filter.mp hp).1).1
    have := (mem_filter.mp hq).2
    omega
  simp only [mass,hs,Finset.sum_union hd]

private theorem mass_bound (a b m : ℕ) (ha : 0<a) :
    mass a b*(m*a:ℕ) ≤ (m*(band a b).card:ℕ) := by
  rw [mass,Finset.sum_mul]
  push_cast
  calc
    _ ≤ ∑ _p ∈ band a b, (m:ℚ) := by
      apply sum_le_sum
      intro p hp
      have hp' : a<p := (mem_filter.mp hp).2
      have hq : (0:ℚ)<p := by exact_mod_cast (by omega : 0<p)
      have hle : (a:ℚ)≤p := by exact_mod_cast hp'.le
      have hh := mul_le_mul_of_nonneg_left hle (show (0:ℚ) ≤ m by positivity)
      calc (1/(p:ℚ))*((m:ℚ)*a) = ((m:ℚ)*a)/p := by ring
           _ ≤ m := (div_le_iff₀ hq).mpr hh
    _ = _ := by simp [mul_comm]

private theorem mass_score (a : ℕ) (ha : 0<a) : mass a (16*a)*(8*a:ℕ) ≤ (score a:ℕ) := by
  rw [mass_split a (2*a) (16*a) (by omega) (by omega),
      mass_split (2*a) (4*a) (16*a) (by omega) (by omega),
      mass_split (4*a) (8*a) (16*a) (by omega) (by omega)]
  have h0 := mass_bound a (2*a) 8 ha
  have h1 := mass_bound (2*a) (4*a) 4 (by omega)
  have h2 := mass_bound (4*a) (8*a) 2 (by omega)
  have h3 := mass_bound (8*a) (16*a) 1 (by omega)
  dsimp [score]
  push_cast at *
  linarith

theorem large_tail (b : ℕ) (hb : 7≤b) :
    let C := 2^b
    ∑ p ∈ (Nat.primesLE (2*C)).filter (C/8 < ·), (1/(p:ℚ)) ≤ 15/16 := by
  let a := 2^(b-3)
  have ha : 0<a := pow_pos (by decide) _
  have hc : (2:ℕ)^b=8*a := by
    dsimp [a]
    conv_lhs => rw [show b=3+(b-3) by omega,pow_add]
    norm_num
  change mass (2^b/8) (2*2^b) ≤ 15/16
  rw [hc,show 8*a/8=a by omega,show 2*(8*a)=16*a by omega]
  have hs : 16*score a≤15*(8*a) := by
    by_cases h : b<11
    · by_cases he : b=7
      · subst b
        decide +kernel
      · have hu := small_scores a (by
          have : 16≤a := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 4≤b-3)
          omega)
        have hq : 16*(8*allowance a+4*allowance (2*a)+2*allowance (4*a)+allowance (8*a)) ≤ 15*(8*a) := by
          dsimp [a]
          have hb' : 8≤b := by omega
          interval_cases b <;> decide +kernel
        omega
    · apply score_bound
      have h : 256≤a := Nat.pow_le_pow_right (by decide : 0<2) (by omega : 8≤b-3)
      omega
  have hh := mass_score a ha
  have hq : (16:ℚ)*(score a:ℕ) ≤ 15*(8*a:ℕ) := by exact_mod_cast hs
  have ht : (0:ℚ)<8*a := by positivity
  push_cast at hh hq
  by_contra! h
  have := mul_lt_mul_of_pos_right h ht
  linarith

end PracticalComplements

namespace PracticalComplements
open Finset

/-- The exact finite families that can meet the complement condition. -/
theorem finite_shape {n : ℕ} (hn : qualifies n) :
    (Odd n ∧ n < 36) ∨ ∃ ph ∈ casesList, primorial (ph.1-1) ∣ n ∧
      (¬ph.1 ∣ n) ∧ n < 4*ph.1^2*(ph.2+3)^2 := by
  classical
  rcases Nat.even_or_odd n with he | ho
  · right
    have hpos : 0 < n := lt_of_lt_of_le (by decide : 0 < 2) hn.1
    have hex : ∃ p : ℕ, p.Prime ∧ ¬p ∣ n := by
      obtain ⟨p,hle,hp⟩ := Nat.exists_infinite_primes (n+1)
      exact ⟨p,hp,fun h => by have := Nat.le_of_dvd hpos h; omega⟩
    let p := Nat.find hex
    have hp : p.Prime ∧ ¬p ∣ n := Nat.find_spec hex
    have hne : p ≠ 2 := fun h => hp.2 (h ▸ even_iff_two_dvd.mp he)
    let b := Nat.log 2 p
    let C := 2^b
    have hC : 0 < C := pow_pos (by decide) _
    have hlo : C ≤ p := Nat.pow_log_le_self _ hp.1.ne_zero
    have hhi : p < 2*C := by
      simpa [C,b,pow_succ, mul_comm] using Nat.lt_pow_succ_log_self (by decide : 1 < 2) p
    have hCp : C < p := by
      apply lt_of_le_of_ne hlo
      intro eq
      have hd : p ∣ 2^b := dvd_of_eq eq.symm
      exact hne ((Nat.prime_dvd_prime_iff_eq hp.1 Nat.prime_two).mp (hp.1.dvd_of_dvd_pow hd))
    have hprim : primorial (p-1) ∣ n := by
      rw [primorial_eq_prod_primesLE]
      apply Finset.prod_primes_dvd n
      · exact fun q hq => Nat.prime_iff.mp (Nat.mem_primesLE.mp hq).2
      · intro q hq
        have hq' := Nat.mem_primesLE.mp hq
        by_contra h
        have hz := Nat.find_min' hex ⟨hq'.2,h⟩
        change p ≤ q at hz
        have := hp.1.two_le
        omega
    by_cases hsmall : p < 128
    · obtain ⟨H,hW,hcases | hlarge⟩ := small_window hp.1 hne hsmall
      · exact ⟨(p,H),hcases,hprim,hp.2,window_cap hn hp.1 hne hp.2 hlo hhi.le hW⟩
      · exact False.elim ((not_lt_of_ge ((Nat.le_of_dvd hpos hprim).trans' hlarge))
          (window_cap hn hp.1 hne hp.2 hlo hhi.le hW))
    · have hb : 7 ≤ b := by
        by_contra! h
        have hz := Nat.pow_le_pow_right (by decide : 0 < 2) (show b ≤ 6 by omega)
        change C ≤ 64 at hz
        omega
      have hw := big_window C p hC (large_tail b hb)
      have hc := window_cap hn hp.1 hne hp.2 hlo hhi.le hw
      have hlarge := large_wheel b hb
      change 4*(2*C)^2*(primorial (C/8)*(32*(2*C)+1)+3)^2 < primorial C at hlarge
      rw [show 32*(2*C)=64*C by ring] at hlarge
      have hcmp := Nat.mul_le_mul_right ((primorial (C/8)*(64*C+1)+3)^2)
        (Nat.mul_le_mul_left 4 (Nat.pow_le_pow_left hhi.le 2))
      have hx : primorial C ≤ n := (primorial_mono (by omega : C ≤ p-1)).trans (Nat.le_of_dvd hpos hprim)
      omega
  · exact Or.inl ⟨ho,odd_cap hn ho⟩

end PracticalComplements

/-! Finite certificates for practical integers and practical complements. -/

namespace PracticalComplements.FiniteProof

private def covered (n last h : ℕ) : Prop :=
  ∀ m ≤ h, ∃ s : Finset ℕ, s ⊆ n.divisors ∧ (∀ i ∈ s, i≤last) ∧ m=∑ i ∈ s, i

private theorem extend {n last h d : ℕ} (hc : covered n last h) (hd : d∈n.divisors)
    (hi : last < d) (hg : d≤h+1) : covered n d (h+d) := by
  intro m hm
  by_cases hmh : m≤h
  · obtain ⟨s,hs,hl,ht⟩ := hc m hmh
    exact ⟨s,hs,fun i h => (hl i h).trans hi.le,ht⟩
  · obtain ⟨s,hs,hl,ht⟩ := hc (m-d) (by omega)
    have hnew : d∉s := fun h => (Nat.not_le_of_gt hi) (hl d h)
    refine ⟨insert d s, Finset.insert_subset hd hs, ?_, ?_⟩
    · intro i him
      rcases Finset.mem_insert.mp him with rfl|h
      · rfl
      · exact (hl i h).trans hi.le
    · rw [Finset.sum_insert hnew, ←ht]
      omega

def chain (n last h : ℕ) : List ℕ → Bool
  | [] => decide (n≤h)
  | d::ds => decide (last<d ∧ d≤h+1 ∧ n%d=0) && chain n d (h+d) ds

theorem chain_practical {n : ℕ} {ds : List ℕ} (hn : 0<n) (ht : chain n 0 0 ds = true) :
    practical n := by
  have go {last h} (xs : List ℕ) (hc : covered n last h) (hh : chain n last h xs = true) :
      practical n := by
    induction xs generalizing last h with
    | nil =>
      have hs : n≤h := of_decide_eq_true hh
      intro m hm
      obtain ⟨s,hs,_,ht⟩ := hc m (hm.trans hs)
      exact ⟨s,hs,ht⟩
    | cons d rest ih =>
      simp only [chain, Bool.and_eq_true, decide_eq_true_eq] at hh
      exact ih (extend hc (Nat.mem_divisors.mpr ⟨Nat.dvd_of_mod_eq_zero hh.1.2.2,hn.ne'⟩)
        hh.1.1 hh.1.2.1) hh.2
  apply go ds _ ht
  intro m hm
  have : m=0 := by omega
  subst m
  exact ⟨∅,by simp,by simp,by simp⟩

def lowTotal (n gap : ℕ) : ℕ :=
  ∑ d ∈ (Finset.range (gap+1)).filter (fun d => n%d=0), d

def misses (n gap : ℕ) : Bool := decide (gap≤n ∧ lowTotal n gap < gap)

theorem misses_not_practical {n gap : ℕ} (h : misses n gap = true) : ¬ practical n := by
  obtain ⟨hle,hlt⟩ : gap≤n ∧ lowTotal n gap < gap := of_decide_eq_true h
  intro hp
  obtain ⟨s,hs,he⟩ := hp gap hle
  have sub : s ⊆ (Finset.range (gap+1)).filter (fun d => n%d=0) := by
    intro d hd
    have hm : d≤∑ i ∈ s, i := Finset.single_le_sum (fun i _ => Nat.zero_le i) hd
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega),
      Nat.mod_eq_zero_of_dvd (Nat.mem_divisors.mp (hs hd)).1⟩
  have hh : (∑ i ∈ s, i) ≤ lowTotal n gap := Finset.sum_le_sum_of_subset sub
  omega

abbrev Reject := ℕ × ℕ × List ℕ

def rejects (n : ℕ) (c : Reject) : Bool :=
  let t := c.1
  decide (0<t ∧ 2*t≤n) && misses t c.2.1 && chain (n-t) 0 0 c.2.2

theorem rejection {n : ℕ} {c : Reject} (h : rejects n c = true) : ¬qualifies n := by
  simp only [rejects, Bool.and_eq_true, decide_eq_true_eq] at h
  intro hn
  have hs := chain_practical (by omega : 0 < n-c.1) h.2
  have hf := hn.2 (n-c.1) (by omega) (by omega) hs
  rw [show n-(n-c.1) = c.1 by omega] at hf
  exact misses_not_practical h.1.2 hf

def checkBlock (p stride start : ℕ) : List Reject → Bool
  | [] => true
  | row::rows =>
    let n := stride*start
    (decide (n<2) || n%p==0 || known.contains n || rejects n row) &&
      checkBlock p stride (start+1) rows

def Block (p stride lo hi : ℕ) : Prop :=
  ∀ j, lo≤j → j<hi → qualifies (stride*j) → ¬p∣stride*j → stride*j∈known

theorem checked_block {p stride lo hi : ℕ} (cs : List Reject) (hlen : hi=lo+cs.length)
    (h : checkBlock p stride lo cs = true) : Block p stride lo hi := by
  subst hi
  induction cs generalizing lo with
  | nil => intro j hj hk; simp at hk; omega
  | cons row rows ih =>
    simp only [checkBlock, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq,
      beq_iff_eq, List.contains_iff_mem] at h
    intro j hj hk hn hp
    by_cases hj0 : j=lo
    · subst j
      rcases h.1 with ((hh|hh)|hh)|hh
      · exact (Nat.not_lt_of_ge hn.1 hh).elim
      · exact (hp (Nat.dvd_of_mod_eq_zero hh)).elim
      · exact hh
      · exact (rejection hh hn).elim
    · exact ih h.2 j (by omega) (by simp only [List.length_cons] at hk; omega) hn hp

theorem join_blocks {p d l m h : ℕ} (a : Block p d l m) (b : Block p d m h) : Block p d l h := by
  intro j hj hk
  by_cases hm : j < m
  · exact a j hj hm
  · exact b j (by omega) hk

-- At t in [1,n/2], certify either that t is practical or that n−t is impractical.
abbrev Accept := ℕ × List ℕ

def checkAccept (n start : ℕ) : List Accept → Bool
  | [] => true
  | row::rows => (chain start 0 0 row.2 || misses (n-start) row.1) &&
      checkAccept n (start+1) rows

theorem checked_accept {n : ℕ} (hn : 2≤n) (rows : List Accept) (hlen : rows.length=n/2)
    (hr : checkAccept n 1 rows = true) : qualifies n := by
  have go (rs : List Accept) (lo : ℕ) (hh : checkAccept n lo rs = true) :
      ∀ t, lo≤t → t<lo+rs.length → 0<t → practical (n-t) → practical t := by
    induction rs generalizing lo with
    | nil => intro t h1 h2; simp at h2; omega
    | cons a as ih =>
      intro t ht hi hpos hp
      simp only [checkAccept, Bool.and_eq_true, Bool.or_eq_true] at hh
      by_cases he : t=lo
      · subst t
        rcases hh.1 with hc|hm
        · exact chain_practical hpos hc
        · exact (misses_not_practical hm hp).elim
      · exact ih (lo+1) hh.2 t (by omega) (by simp only [List.length_cons] at hi; omega) hpos hp
  refine ⟨hn, fun s hs hsn hp => ?_⟩
  exact go rows 1 hr (n-s) (by omega) (by omega) (by omega) (by simpa [show n-(n-s)=s by omega] using hp)

end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof



set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_2 : qualifies 2 :=
  checked_accept (by decide +kernel) [(0,[1])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_3 : qualifies 3 :=
  checked_accept (by decide +kernel) [(0,[1])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_4 : qualifies 4 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_5 : qualifies 5 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_6 : qualifies 6 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_8 : qualifies 8 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_10 : qualifies 10 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_12 : qualifies 12 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_14 : qualifies 14 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_16 : qualifies 16 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_18 : qualifies 18 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_20 : qualifies 20 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_24 : qualifies 24 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_36 : qualifies 36 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16]),(2,[]),(0,[1,2,3,6,9])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_48 : qualifies 48 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16]),(2,[]),(0,[1,2,3,6,9]),(2,[]),(0,[1,2,4,5,10]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,12])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_60 : qualifies 60 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16]),(2,[]),(0,[1,2,3,6,9]),(2,[]),(0,[1,2,4,5,10]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,12]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,7,14]),(2,[]),(0,[1,2,3,6,10,15])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_72 : qualifies 72 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16]),(2,[]),(0,[1,2,3,6,9]),(2,[]),(0,[1,2,4,5,10]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,12]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,7,14]),(2,[]),(0,[1,2,3,6,10,15]),(2,[]),(0,[1,2,4,8,16,32]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6,12,18])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_84 : qualifies 84 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16]),(2,[]),(0,[1,2,3,6,9]),(2,[]),(0,[1,2,4,5,10]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,12]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,7,14]),(2,[]),(0,[1,2,3,6,10,15]),(2,[]),(0,[1,2,4,8,16,32]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6,12,18]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,10,20]),(2,[]),(0,[1,2,3,7,14,21])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_96 : qualifies 96 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16]),(2,[]),(0,[1,2,3,6,9]),(2,[]),(0,[1,2,4,5,10]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,12]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,7,14]),(2,[]),(0,[1,2,3,6,10,15]),(2,[]),(0,[1,2,4,8,16,32]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6,12,18]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,10,20]),(2,[]),(0,[1,2,3,7,14,21]),(2,[]),(8,[]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16,24])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem accepted_120 : qualifies 120 :=
  checked_accept (by decide +kernel) [(0,[1]),(0,[1,2]),(2,[]),(0,[1,2,4]),(2,[]),(0,[1,2,3]),(2,[]),(0,[1,2,4,8]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16]),(2,[]),(0,[1,2,3,6,9]),(2,[]),(0,[1,2,4,5,10]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,12]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,7,14]),(2,[]),(0,[1,2,3,6,10,15]),(2,[]),(0,[1,2,4,8,16,32]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6,12,18]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,10,20]),(2,[]),(0,[1,2,3,7,14,21]),(2,[]),(8,[]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,8,16,24]),(2,[]),(4,[]),(2,[]),(8,[]),(2,[]),(0,[1,2,3,6,9,18,27]),(2,[]),(0,[1,2,4,8,14,28]),(2,[]),(4,[]),(2,[]),(0,[1,2,4,6,12,20,30])]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem known_qualifies : ∀ n∈known, qualifies n := by
  simp only [known, List.forall_mem_cons, List.not_mem_nil, forall_false, implies_true, and_true]
  exact ⟨accepted_2,accepted_3,accepted_4,accepted_5,accepted_6,accepted_8,accepted_10,accepted_12,accepted_14,accepted_16,accepted_18,accepted_20,accepted_24,accepted_36,accepted_48,accepted_60,accepted_72,accepted_84,accepted_96,accepted_120⟩

end PracticalComplements.FiniteProof

/-! Compact encoding of the explicit divisor witnesses.  Every decoded row goes through
`checkBlock`, so the encoding needs no mathematical correctness assumption. -/

namespace PracticalComplements.FiniteProof

private def decodeChain (n : ℕ) : ℕ → ℕ → ℕ → ℕ → List ℕ
  | 0, _, _, _ => []
  | fuel+1, last, h, code =>
    if code=0 then [] else
    let bound := n / max 1 last + 1
    let radix := min (h+2) bound
    let arg := code / 4 % radix
    let (d, rest) := if code%2=1 then (2*last,code/2)
      else if code%4=2 then (3*last/2,code/4)
      else (if h+2≤bound then arg else n/arg,code/4/radix)
    d :: decodeChain n fuel d (h+d) rest

private def expandRows (stride : ℕ) : ℕ → List ℕ → List Reject
  | _, [] => []
  | j, c::cs =>
    let t := c%1024
    (t,c/1024%1024,decodeChain (stride*j-t) 64 0 0 (c/1048576)) :: expandRows stride (j+1) cs

private theorem length_expand (s j : ℕ) (cs : List ℕ) : (expandRows s j cs).length=cs.length := by
  induction cs generalizing j with
  | nil => rfl
  | cons c cs ih => simp only [expandRows, List.length_cons, ih]

theorem checked_packed {p stride lo hi : ℕ} (cs : List ℕ) (hlen : hi=lo+cs.length)
    (h : checkBlock p stride lo (expandRows stride lo cs) = true) : Block p stride lo hi :=
  checked_block _ (by simpa only [length_expand] using hlen) h

end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_0_0 : Block 0 1 0 32 :=
  checked_packed [
    0,0,0,0,
    0,0,0,29362179,
    0,46139395,0,62916611,
    0,62916613,0,96471043,
    0,96471045,0,130025475,
    0,381683715,96473098,1371539459,
    0,1371539461,130027530,197134339,
    381685770,197134341,1371541514,1639974915]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_0_32 : Block 0 1 32 36 :=
  checked_packed [
    381685774,8166311939,197136394,264243203]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_0 : Block 3 2 0 32 :=
  checked_packed [
    0,0,0,0,
    0,0,0,0,
    0,0,0,96473098,
    0,130027530,381685770,0,
    381685774,197136394,0,1639976970,
    8166313994,0,8166313998,767561738,
    0,2747273226,12662607882,0,
    12662607886,398462986,0,398462990]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_32 : Block 3 2 32 64 :=
  checked_packed [
    3066040330,0,3066040334,16336818186,
    0,532680714,35546730506,0,
    35546730510,1539313674,0,1539313678,
    44673536010,0,44673536014,14256443402,
    0,11874078730,18194668457994,0,
    18194668457998,801116170,0,197597859850,
    18194668458006,0,18194668458010,6136270858,
    0,6572478474,18194668458018,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_64 : Block 3 2 64 96 :=
  checked_packed [
    18194668458022,15095304202,0,15095304206,
    98561953802,0,98561953806,71097651210,
    0,71097651214,98561953814,0,
    98561953818,3082817546,0,3082817550,
    3658351644682,0,3658351644686,95659495434,
    0,11001663498,24540876810,0,
    24540876814,54018445322,0,54018445326,
    24540876822,0,24540876826,971967041546]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_96 : Block 3 2 96 128 :=
  checked_packed [
    0,971967041550,24540876834,0,
    24540876838,1606422538,0,236521000970,
    344247504906,0,344247504910,225716473866,
    0,26973573130,2091426779146,0,
    2091426779150,69990354954,0,11080105463818,
    2091426779158,0,2091426779162,249338793994,
    0,249338793998,345321246730,0,
    345321246734,30194798602,0,30194798606]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_128 : Block 3 2 128 160 :=
  checked_packed [
    345321246742,0,345321246746,110893207562,
    0,2143293450,345321246754,0,
    345321246758,142199492618,0,142199492622,
    111780884457197578,0,111780884457197582,296583434250,
    0,747655663626,111780884457197590,0,
    111780884457197594,6169825290,0,6169825294,
    5578940223498,0,5578940223502,320205754378,
    0,83881889802,1740380311562,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_160 : Block 3 2 160 192 :=
  checked_packed [
    1740380311566,108510842890,0,108510842894,
    1740380311574,0,1740380311578,49085943818,
    0,49085943822,7319274393610,0,
    7319274393614,136495239178,0,28376878288906,
    2263829450762,0,2263829450766,108741772972042,
    0,47508885514,2263829450774,0,
    2263829450778,109047713802,0,13127865339914,
    2263829450786,0,2263829450790,98914275342]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_192 : Block 3 2 192 224 :=
  checked_packed [
    0,13127865339926,177746999250954,0,
    177746999250958,3217035274,0,3217035278,
    7320348135434,0,7320348135438,1328449327114,
    0,106430468106,7320348135446,0,
    7320348135450,133609558026,0,133609558030,
    4716792647690,0,4716792647694,15148781670410,
    0,15148781670414,4716792647702,0,
    4716792647706,113946660874,0,113946660878]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_224 : Block 3 2 224 256 :=
  checked_packed [
    4716792647714,0,4716792647718,1495248408590,
    0,26302484490,11625198972091502602,0,
    11625198972091502606,498681778186,0,38028475109386,
    11596862448472074,0,11596862448472078,739904589834,
    0,739904589838,11596862448472086,0,
    11596862448472090,60393787402,0,60393787406,
    196339568650,0,196339568654,60393787414,
    0,128979046410,196339568662,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_256 : Block 3 2 256 288 :=
  checked_packed [
    196339568666,419090665482,0,419090665486,
    702589117141002,0,702589117141006,4290777102,
    0,1495785279498,5876433817610,0,
    5876433817614,284403175434,0,37770240200714,
    5876433817622,0,5876433817626,37130222964746,
    0,152735584266,13354637943902218,0,
    13354637943902222,593171058698,0,593171058702,
    6262980874250,0,6262980874254,2902991048718]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_288 : Block 3 2 288 320 :=
  checked_packed [
    0,593171058714,702649246683146,0,
    702649246683150,12343840778,0,94901626736650,
    702649246683158,0,702649246683162,4913740386314,
    0,4913740386318,2749429190666,0,
    2749429190670,2226466590730,0,2226466590734,
    2749429190678,0,2749429190682,3480764813322,
    0,42584932093962,2749429190690,0,
    2749429190694,421573693450,0,421573693454]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_320 : Block 3 2 320 352 :=
  checked_packed [
    8268683700867082,0,8268683700867086,421573693462,
    0,44019224586,8268683700867094,0,
    8268683700867098,745373962250,0,745373962254,
    8268683700867106,0,8268683700867110,28232124469258,
    0,28232124469262,7422622044170,0,
    7422622044174,272994668554,0,272994668558,
    7422622044182,0,7422622044186,2658815447050,
    0,2658815447054,702769505767434,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_352 : Block 3 2 352 384 :=
  checked_packed [
    702769505767438,1533768896522,0,49018759548938,
    2750502932490,0,2750502932494,95021961230,
    0,49018759548950,803497964474378,0,
    803497964474382,423721177098,0,423721177102,
    31852127588362,0,31852127588366,49594318721038,
    0,197832740874,31852127588374,0,
    31852127588378,1632553144330,0,1632553144334,
    3042845929771018,0,3042845929771022,52768265998346]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_384 : Block 3 2 384 416 :=
  checked_packed [
    0,119029981253642,3042845929771030,0,
    3042845929771034,6438260746,0,6438260750,
    3042845929771042,0,3042845929771046,15686390779914,
    0,3469926731786,3042845929771054,0,
    52768266002476,3324770258954,0,3324770258958,
    892558406324234,0,892558406324238,212865126414,
    0,3324770258970,2103266196623502348298,0,
    2103266196623502348302,560891695114,0,132705928876042]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_416 : Block 3 2 416 448 :=
  checked_packed [
    2103266196623502348310,0,2103266196623502348314,2663110414346,
    0,107906863114,2103266196623502348322,0,
    2103266196623502348326,1788379926538,0,1788379926542,
    56814930501676,0,560891699244,1788379926550,
    0,1788379926554,31853201330186,0,
    31853201330190,227897511946,0,121148440317962,
    3510413249482762,0,3510413249482766,227897511958,
    0,5805315198986,134221800673290,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_3_448 : Block 3 2 448 450 :=
  checked_packed [
    134221800673294,1928905887754]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_0 : Block 5 6 0 32 :=
  checked_packed [
    0,0,0,0,
    0,0,0,264245258,
    0,2747273230,0,3284144138,
    0,532680718,0,0,
    0,11874078734,532684844,13484691466,
    0,6572478478,11874082860,1069551626,
    197597863980,0,6572482604,197866295318,
    197597864004,11001663502,0,23752347658]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_32 : Block 5 6 32 64 :=
  checked_packed [
    197866299444,23752347670,11001667628,0,
    197866299468,26973573134,23752351796,13149147146,
    0,13149147158,26973577260,13149147170,
    11080105467948,0,13149151284,76365697034,
    11080105467972,747655663630,0,747655663642,
    11089769144372,11272439468042,747655667756,0,
    11089769144396,22007517206,83881893932,28376878288910,
    0,47508885518,22007521332,98914275338]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_64 : Block 5 6 64 96 :=
  checked_packed [
    28376878293036,0,47508889644,893684551690,
    13127865344044,106430468110,0,53951336458,
    31507909451828,53951336470,106430472236,0,
    31507909451852,26302484494,53951340596,121462853642,
    0,34020733751306,26302488620,34020733751318,
    38028475113516,0,121462857780,4290777098,
    34020733755444,1495785279502,0,37770240200718,
    82300192694324,152735584270,1495785283628,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_96 : Block 5 6 96 128 :=
  checked_packed [
    37770240204844,2902991048726,152735588396,94901626736654,
    0,94901626736666,2902991052852,167767969802,
    94901626740780,0,2902991052876,101202343759894,
    94901626740804,45269253099530,0,45269253099542,
    101202343764020,45269253099554,44019228716,0,
    45269253103668,4543333011478,44019228740,95021961226,
    0,95021961238,4543333015604,49594318721034,
    49018759553068,0,95021965364,120104494829590]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_128 : Block 5 6 128 160 :=
  checked_packed [
    49018759553092,119029981253646,0,119029981253658,
    120104494833716,3469926731790,119029981257772,0,
    120104494833740,56814930497546,3469926735916,132705928876046,
    0,107906863118,212865130548,107906863130,
    132705928880172,0,107906867244,121148440317966,
    132705928880196,5805315198990,0,52609159178,
    121148440322092,52609159190,5805315203116,0,
    121148440322116,242929897486,52609163316,242929897498]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_160 : Block 5 6 160 192 :=
  checked_packed [
    0,128522932719630,242929901612,6460230602762,
    134221800682598,0,128522932723756,257962283018,
    3510413249492106,161620219138062,0,161620219138074,
    113804046245940,8585744398,161620219142188,0,
    113804046245964,5807462682646,8585748524,142687734861834,
    0,142687734861846,5807462686772,305475358730,
    143761443135556,0,142687734865972,4608825415962646,
    143761443135580,6322456104974,0,6322456104986]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_192 : Block 5 6 192 224 :=
  checked_packed [
    4608825415966772,158836778340362,6322456109100,0,
    4608825415966796,358517357678614,6460767477804,646656823306,
    0,646656823318,358517357682740,166374445944846,
    158836778344524,0,646656827444,165330064248842,
    166374445948972,382320066433038,0,382320066433050,
    166374445948996,382320066433062,382320066437164,0,
    166374445949020,171017339146254,382320066437188,95692464223948814,
    0,181449781153802,171017339150380,181449781153814]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_224 : Block 5 6 224 256 :=
  checked_packed [
    95692464223952940,0,711081336876,7336940802058,
    181449781157940,37021137506318,0,743293587466,
    181449781157964,743293587478,37021137510444,0,
    188987448762412,190048112654,743293591604,190048112666,
    0,190048112678,190048116780,190048112690,
    188987448762460,0,190048116804,395669671946,
    629414851277501542,204062783967242,0,464260794683402,
    11240426669356134,807718096910,453728192700460,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_256 : Block 5 6 256 288 :=
  checked_packed [
    204062783971380,462116599369750,807718101036,211600451571726,
    0,211600451571738,462116599373876,10499311800330,
    211600451575852,0,462116599373900,10499311800354,
    211600451575876,425734443022,0,425734443034,
    211600451575900,221785194762254,425734447148,0,
    6781955001562214,562583601942550,221785194766380,215817916426,
    0,515662963281934,562583601946676,515662963281946,
    12644571737502834,0,515662963286060,1038779622008819734]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_288 : Block 5 6 288 320 :=
  checked_packed [
    12644571737502858,562656616386574,0,457672046415882,
    1038779622008823860,457672046415894,562656616390700,0,
    1038779622008823884,527637868974094,457672046420020,527637868974106,
    0,105222508558,527637868978220,105222508570,
    7495538047988838,0,105222512684,26402482821271574,
    1788495361870935178,11616942821390,0,485863985162,
    26402482821275700,485863985174,11616942825516,0,
    26402482821275724,1000991625230,485863989300,498971713736714]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_320 : Block 5 6 320 352 :=
  checked_packed [
    0,498971713736726,1000991629356,498971713736738,
    1153414094435393580,0,498971713740852,1033203879946,
    1153414094435393604,429926557683726,0,586049424199690,
    1153414094435393628,515928756238,429926557687852,0,
    7644733199365222,11618016563222,515928760364,723630916898826,
    0,723630916898838,11618016567348,17175678986,
    16147787956084552818,0,723630916902964,543098945933322,
    8926466532193394,22878481289230,0,22878481289242]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_352 : Block 5 6 352 384 :=
  checked_packed [
    15920910229845094,22878481289254,22878481293356,0,
    11618016575624,553964474994702,22878481293380,553964474994714,
    0,10460876331028490,553964474998828,10460876331028502,
    3948991840237071119474,0,553964474998852,610954907674,
    10460876331032628,723667424120846,0,723667424120858,
    10460876331032652,723667424120870,723667424124972,0,
    7107891479721074,12644916400150,723667424124996,12644916400162,
    0,12644916400174,12644916404276,25083275907082]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_384 : Block 5 6 384 416 :=
  checked_packed [
    12029948086662740325490,0,12644916404300,15801726682533910,
    19279966235538534,11620164046862,0,11620164046874,
    15801726682538036,11620164046886,11620164050988,0,
    15801726682538060,1293317836814,11620164051012,60457723040370702,
    0,702872534650894,1293317840940,628525845450762,
    60457723040374828,0,702872534655020,671084449802,
    60457723040374852,1483231853547534,0,1483231853547546,
    1783211098300751924,651300916170766,1483231853551660,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_416 : Block 5 6 416 448 :=
  checked_packed [
    1783211098300751948,11621237788694,651300916174892,57939330043219982,
    0,57939330043219994,11621237792820,57939330043220006,
    57939330043224108,0,11621237792844,1549693519663114,
    57939330043224132,176089468942,0,663949997510666,
    1218181484267970604,663949997510678,176089473068,0,
    1218181484267970628,761284089876502,663949997514804,1422166855690,
    0,685477111795726,761284089880628,685477111795738,
    22135397932872806,0,685477111799852,62206519906668566]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_448 : Block 5 6 448 480 :=
  checked_packed [
    744749052998770,1626486192738318,0,1626486192738330,
    62206519906672692,28484890005518,1626486192742444,0,
    62206519906672716,1652789914636302,28484890009644,713952744968202,
    0,1486591365134,1652789914640428,1486591365146,
    62206519906672764,0,1486591369260,1486591365170,
    11976615739274342,718942758768654,0,380100415498,
    28168351596786234470,380100415510,718942758772780,0,
    1994459995483056125030,1721989085532182,380100419636,1783211107964424206]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_480 : Block 5 6 480 512 :=
  checked_packed [
    0,1783211107964424218,1721989085536308,1783211107964424230,
    1783211107964428332,0,1721989085536332,758503299878922,
    1783211107964428356,1769740531929102,0,1769740531929114,
    57939407352635444,791343534094,1769740531933228,0,
    57939407352635468,770904011313166,791343538220,770904011313178,
    0,1802424494854158,770904011317292,1615440384010,
    57939407352635516,0,1802424494858284,880539493994522,
    758503299891336,331421415641102,0,331421415641114]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_512 : Block 5 6 512 544 :=
  checked_packed [
    3721670161422365798,331421415641126,331421415645228,0,
    25704687554540658,799379644485654,331421415645252,57939446007336974,
    0,57939446007336986,799379644489780,57939446007336998,
    57939446007341100,0,799379644489804,20998627790874,
    57939446007341124,1912994871119886,0,1912994871119898,
    57939446007341148,1912994871119910,1912994871124012,0,
    12225161201726578,851473076246,1912994871124036,1877674939125770,
    0,1877674939125782,851473080372,13887906779146]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_544 : Block 5 6 544 576 :=
  checked_packed [
    52804961049780268,0,1877674939129908,1962079099555866,
    52804961049780292,2463062942552078,0,2463062942552090,
    52804961049780316,1717025177079822,2463062942556204,0,
    643482780005870613606,31571293425897482,1717025177083948,2001985855295498,
    0,2001985855295510,431640027180,2001985855295522,
    31571293425901620,0,2001985855299636,1808713912330,
    31571293425901644,23155913049247758,0,1774122472312842,
    3263694654381498412,1774122472312854,23155913049251884,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_576 : Block 5 6 576 608 :=
  checked_packed [
    3263694654381498436,2463204676472854,1774122472316980,2463204676472866,
    0,13888980520974,2463204676476980,13888980520986,
    31139479041356902,0,13888980525100,52805038359187478,
    1808713924744,1873138421774,0,2048476728791050,
    52805038359191604,2048476728791062,1873138425900,0,
    52805038359191628,2203805243265001721878,2048476728795188,210449207306,
    0,210449207318,2203805243265001726004,2168271889502218,
    15545064621094002,0,210449211444,2168271889502242]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_608 : Block 5 6 608 640 :=
  checked_packed [
    15545064621094026,113498561282314254,0,113498561282314266,
    30701693024875622,113498561282314278,113498561282318380,0,
    2203805243265001734280,45764214525974,113498561282318404,57939561971453966,
    0,971732160526,45764214530100,35050835410948110,
    57939561971458092,0,971732164652,1945414358011914,
    35050835410952236,2463488144314382,0,2001987440650,
    1087507725849468980,2271368284475406,2463488144318508,0,
    1087507725849469004,297937850601486,2271368284479532,297937850601498]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_640 : Block 5 6 640 672 :=
  checked_packed [
    0,297937850601510,297937850605612,2229020443807754,
    1380459736412404593766,0,297937850605636,98804913147914,
    1945414358024328,98804913147926,0,98804913147938,
    2001987453064,2066411950094,98804913152052,0,
    904836711199846,1669126963597334,2066411954220,1669126963597346,
    0,2275251002019854,1669126963601460,1031861702666,
    52882224319713775727730,0,2275251002023980,2059608948477978,
    12998662464484454,3263694809000316938,0,3263694809000316950]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_672 : Block 5 6 672 704 :=
  checked_packed [
    61146075653747850,3263694809000316962,45768509497388,0,
    3263694809000321076,50168569270286,45768509497412,27313020988297230,
    0,27313020988297242,50168569274412,2116706243710986,
    27313020988301356,0,50168569274436,57939639280865302,
    27313020988301380,57939639280865314,0,2584609376178186,
    57939639280869428,2108502117978126,34355552324,0,
    57939639280869452,46433424117782,2108502117982252,287728862972950351886,
    0,287728862972950351898,46433424121908,287728862972950351910]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_704 : Block 5 6 704 736 :=
  checked_packed [
    287728862972950356012,0,46433424121932,287728862972950351934,
    287728862972950356036,18563806024175630,0,2182284958502922,
    287728862972950356060,2463250780262414,18563806024179756,0,
    287728862972950356084,4664867164174,2463250780266540,57939677935570958,
    0,53144456773242894,4664867168300,53144456773242906,
    57939677935575084,0,53144456773247020,1221914005514,
    57939677935575108,1221914005526,0,1221914005538,
    110423452711657524,1221914005550,1221914009652,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_736 : Block 5 6 736 768 :=
  checked_packed [
    110423452711657548,2696147059609622,1221914009676,2287998129410058,
    0,2287998129410070,2696147059613748,2287998129410082,
    1266231014145925164,0,2287998129414196,2580365948489738,
    1266231014145925188,25289836990478,0,25289836990490,
    1266231014145925212,42009919381049354,25289836994604,0,
    81542196737619058,42009919381049378,25289836994628,4931155136522,
    0,4931155136534,25289836994652,4931155136546,
    42009919381053516,0,4931155140660,2329607034376202]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_768 : Block 5 6 768 800 :=
  checked_packed [
    2580365948502152,107815284731023374,0,107815284731023386,
    42009919381053564,161284741926926,107815284731027500,0,
    74474893550302310,2402192719876110,161284741931052,5581551119110154,
    0,5064299122702,2402192719880236,5064299122714,
    70384860618830950,0,5064299126828,11124111134431383574,
    2329607034388616,5573041782263822,0,2586639863818,
    11124111134431387700,2586639863830,5573041782267948,0,
    4483121820601425964,2459290015109142,2586639867956,2728799548477450]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_800 : Block 5 6 800 832 :=
  checked_packed [
    0,2728799548477462,2459290015113268,2728799548477474,
    4483121820601426012,0,2728799548481588,2440159492575258,
    4483121820601426036,2679957113278478,0,2679957113278490,
    86534557471118427436134,1342173089806,2679957113282604,0,
    2459290015121544,2814596284944398,1342173093932,4548740966604869646,
    0,4548740966604869658,2814596284948524,1563072275681290,
    4548740966604873772,0,2814596284948548,1413460603267190806,
    4548740966604873796,45781394395150,0,45781394395162]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_832 : Block 5 6 832 864 :=
  checked_packed [
    1413460603267194932,2573484605575182,45781394399276,0,
    1413460603267194956,116773280840421398,2573484605579308,116773280840421410,
    0,116773280840421422,116773280840425524,116773280840421434,
    392276415379970995314,0,116773280840425548,178321110722265747478,
    392276415379970995338,178321110722265747490,0,7299751726855229450,
    178321110722265751604,50171790495758,5463731085380,0,
    178321110722265751628,352183128086,50171790499884,352183128098,
    0,2615561259323406,352183132212,161285815668746]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_864 : Block 5 6 864 896 :=
  checked_packed [
    239375589082131773535334,0,2615561259327532,6201005662277642,
    30905727392429194,2955573821706254,0,2955573821706266,
    105609975488847924,2955573821706278,2955573821710380,0,
    105609975488847948,2844337901582,2955573821710404,2661264408973322,
    0,2661264408973334,2844337905708,2661264408973346,
    307254171634809970756,0,2661264408977460,5730019053578,
    307254171634809970780,2744776491274254,0,2744776491274266,
    15991301312734044212,2744776491274278,2744776491278380,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_896 : Block 5 6 896 928 :=
  checked_packed [
    15991301312734044236,6407490510000142,2744776491278404,6407490510000154,
    0,6407490510000166,6407490510004268,112213801046026,
    86534560380426194531442,0,6407490510004292,2801873786507274,
    56025684362933350,5863163039758,0,50172864237578,
    2744776491286680,50172864237590,5863163043884,0,
    2569829407648322172018,2771816867172366,50172864241716,2973186920458,
    0,3287300922413070,2771816867176492,3287300922413082,
    464893833891993886764,0,3287300922417196,3287300922413106]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_928 : Block 5 6 928 960 :=
  checked_packed [
    464893833891993886788,3287300922413118,0,3287300922413130,
    464893833891993886812,3287300922413142,3287300922417244,0,
    464893833891993886836,2832199409733654,3287300922417268,2832199409733666,
    0,760205021198,2832199409737780,760205021210,
    1306158455338086,0,760205025324,2916068376973338,
    1428093749732324454,45357037592252426,0,6129451012106,
    34686282631787623494758,6129451012118,6685369592455212,0,
    45357037592256564,3287373936857110,6129451016244,105610052798255118]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_960 : Block 5 6 960 992 :=
  checked_packed [
    0,105610052798255130,3287373936861236,2973165672206346,
    105610052798259244,0,3287373936861260,13744522618613010454,
    105610052798259268,77440107782606862,0,77440107782606874,
    13744522618613014580,2147089043689486,77440107782610988,0,
    13744522618613014604,341384389149534982154,2147089043693612,341384389149534982166,
    0,341384389149534982178,6870757560819764,1582691258378,
    341384389149534986292,0,6870757560819788,15991321722418630678,
    341384389149534986316,6939373555683342,0,2992921783570442]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_992 : Block 5 6 992 1024 :=
  checked_packed [
    15991321722418634804,2992921783570454,6939373555687468,0,
    15991321722418634828,2992921783570478,2992921783574580,595872215732234,
    0,3087360262672398,2992921783574604,3087360262672410,
    921809720051731800108,0,3087360262676524,56975018692618,
    921809720051731800132,56975018692630,0,56975018692642,
    105610091452964916,56975018692654,56975018696756,0,
    105610091452964940,6528882970646,56975018696780,3144457557905418,
    0,3144457557905430,6528882974772,3144457557905442]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1024 : Block 5 6 1024 1056 :=
  checked_packed [
    15991328525646831660,0,3144457557909556,7043300825501722,
    15991328525646831684,3103474241769486,0,3103474241769498,
    15991328525646831708,385916096734442819594,3103474241773612,0,
    1431571500381298,6662026956814,3103474241773636,6662026956826,
    0,6662026956838,6662026960940,7439914748612618,
    385916096734442823756,0,6662026960964,41997259771914,
    214755180690814066,41997259771926,0,41997259771938,
    411326990028491155038024806,41997259771950,41997259776052,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1056 : Block 5 6 1056 1088 :=
  checked_packed [
    82581492873576584,3258652148371470,41997259776076,7277823219732490,
    0,7277823219732502,3258652148375596,7277823219732514,
    80463134702568988488818,0,7277823219736628,510921207384683581462,
    41997259784328,1702950342670,0,1702950342682,
    510921207384683585588,7646399596335118,1702950346796,0,
    510921207384683585612,56976092434446,7646399596339244,6928314929162,
    0,6928314929174,56976092438572,6928314929186,
    13744522695922425900,0,6928314933300,7617483796123658]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1088 : Block 5 6 1088 1120 :=
  checked_packed [
    13744522695922425924,7617483796123670,0,7617483796123682,
    1000057379423768289332,7617483796123694,7617483796127796,0,
    1000057379423768289356,91543197192214,7617483796127820,105610168762372110,
    0,7061458915342,91543197196340,3389014941896714,
    105610168762376236,0,7061458919468,3389014941896738,
    105610168762376260,8645514283192334,0,863284236298,
    105610168762376284,236482338463158286,8645514283196460,0,
    105610168762376308,7886611412946958,236482338463162412,15991348935331418126]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1120 : Block 5 6 1120 1152 :=
  checked_packed [
    0,15991348935331418138,7886611412951084,15991348935331418150,
    15991348935331422252,0,7886611412951108,15991348935331418174,
    15991348935331422276,3157472114118670,0,24446448503311306762,
    15991348935331422300,3617432014862,3157472114122796,0,
    15991348935331422324,1664802468401174,3617432018988,924168143673007017998,
    0,6887769926275086,1664802468405300,7327746887690,
    924168143673007022124,0,6887769926279212,105610207417077782,
    924168143673007022148,91545344675854,0,91545344675866]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1152 : Block 5 6 1152 1184 :=
  checked_packed [
    105610207417081908,91545344675878,91545344679980,0,
    105610207417081932,428784053990266507290,91545344680004,54714926370826,
    0,8265854139502606,91545344680028,7981390402424842,
    428784053990266511428,0,8265854139506732,177162162278410,
    428784053990266511452,395532038360272910,0,395532038360272922,
    2952468905110649451622,395532038360272934,395532038360277036,0,
    107938104739902578,3746281033750,395532038360277060,3746281033762,
    0,8069757408382990,3746281037876,6527389613407866894]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1184 : Block 5 6 1184 1216 :=
  checked_packed [
    7981390402437256,0,8069757408387116,32654872486671814678,
    6527389613407871020,8646364686716942,0,8646364686716954,
    32654872486671818804,8646364686716966,8646364686721068,0,
    32654872486671818828,420902604814,8646364686721092,420902604826,
    0,420902604838,420902608940,420902604850,
    384597938810289523799154,0,420902608964,7727178846218,
    384597938810289523799178,7727178846230,0,133410671730626574,
    17035584336155385908,133410671730626586,7727178850356,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1216 : Block 5 6 1216 1248 :=
  checked_packed [
    133410671730630700,440641473541574678,7727178850380,8678823834947594,
    0,8678823834947606,440641473541578804,8678823834947618,
    34299974703411896364,0,8678823834951732,8678823834947642,
    34299974703411896388,7860322832398,0,7860322832410,
    34299974703411896412,8450435190886414,7860322836524,0,
    34299974703411896436,98005648146436118,8450435190890540,1943468511242,
    0,1943468511254,98005648146440244,262545574404821002,
    105610284726493228,0,1943468515380,262545574404821026]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1248 : Block 5 6 1248 1280 :=
  checked_packed [
    105610284726493252,8885308682670094,0,8885308682670106,
    105610284726493276,7552785482518542,8885308682674220,0,
    515409505660449894,91549639643158,7552785482522668,723509909685543112718,
    0,4003979071502,91549639647284,8818253572870154,
    723509909685543116844,0,4003979075628,8684957585117194,
    723509909685543116868,1848489629716494,0,8126610804746,
    723509909685543116892,8126610804758,1848489629720620,0,
    723509909685543116916,8126610804782,8126610808884,8126610804794]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1280 : Block 5 6 1280 1312 :=
  checked_packed [
    0,8126610804806,8126610808908,8126610804818,
    2622524371444446322,0,48195163323929474150,105610323381194774,
    48195163323929474162,105610323381194786,0,105610323381194798,
    105610323381198900,8259754790926,8653844372267076,0,
    105610323381198924,18218542193184790,8259754795052,18218542193184802,
    0,18218542193184814,18218542193188916,4132828090378,
    26853590980473402470,0,18218542193188940,9718166192132106,
    105610323381198996,6575349307543566,0,6575349307543578]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1312 : Block 5 6 1312 1344 :=
  checked_packed [
    359842378079522529332,6575349307543590,6575349307547692,0,
    359842378079522529356,161291184377870,6575349307547716,8963110605950986,
    0,8963110605950998,161291184381996,8963110605951010,
    37080998325725962284,0,8963110605955124,7996129186680842,
    37080998325725962308,7996129186680854,0,7996129186680866,
    37080998325725962332,7996129186680878,7996129186684980,0,
    37080998325725962356,24446449671542411278,7996129186685004,24446449671542411290,
    0,147400582804541450,24446449671542415404,147400582804541462]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1344 : Block 5 6 1344 1376 :=
  checked_packed [
    13437212811331646578,0,24446449671542415428,772979051630289752086,
    147400582804545588,18961227938009102,0,197634258112522,
    772979051630289756212,197634258112534,18961227938013228,0,
    30308139720473845804,8659186749454,197634258116660,1096787932723407753230,
    0,1096787932723407753242,8659186753580,1096787932723407753254,
    1096787932723407757356,0,8659186753604,68715286538,
    1096787932723407757380,19617652652843733006,0,9388524767809546,
    1096787932723407757404,9388524767809558,19617652652843737132,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1376 : Block 5 6 1376 1408 :=
  checked_packed [
    1096787932723407757428,19332570810421270,9388524767813684,210354912054218766,
    0,11037682754916366,19332570810425396,8306221127831562,
    210354912054222892,0,11037682754920492,38935014073935335446,
    210354912054222916,92866852425742,0,92866852425754,
    38935014073935339572,92866852425766,92866852429868,0,
    38935014073935339596,94671599352926177333258,92866852429892,94671599352926177333270,
    0,94671599352926177333282,40953555049716391988,94671599352926177333294,
    94671599352926177337396,0,40953555049716392012,161292258119690]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1408 : Block 5 6 1408 1440 :=
  checked_packed [
    94671599352926177337420,161292258119702,0,161292258119714,
    154395538341503020,208910560530446,161292258123828,0,
    154395538341503044,91556082094102,208910560534572,20137107961514299406,
    0,8661993938489358,91556082098228,9563209207910410,
    20137107961514303532,0,8661993938493484,26190893216937545750,
    20137107961514303556,20075256555245582,0,9329738518538,
    26190893216937549876,9329738518550,20075256555249708,0,
    26190893216937549900,20551807627406872598,9329738522676,206325538388709386]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1440 : Block 5 6 1440 1472 :=
  checked_packed [
    0,9857569556271118,20551807627406876724,9857569556271130,
    67218765528822454432882,0,9857569556275244,9857569556271154,
    54200999162612298854,1643433218550009870,0,1643433218550009882,
    13982297260612924518,2443832201230,1643433218550013996,0,
    20551807627406885000,20446599427657750,2443832205356,9292136963769372686,
    0,9292136963769372698,20446599427661876,9292136963769372710,
    9292136963769376812,0,20446599427661900,9292136963769372734,
    9292136963769376836,91558229577742,0,177165383503882]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1472 : Block 5 6 1472 1504 :=
  checked_packed [
    9292136963769376860,177165383503894,91558229581868,0,
    9292136963769376884,8882816595005454,177165383508020,8882816595005466,
    0,8882816595005478,8882816595009580,21089234915954698,
    9292136963769376932,0,8882816595009604,41716037696249401366,
    267483246294479986,41716037696249401378,0,3376236117035585550,
    41716037696249405492,10017891625734158,21089234915958860,0,
    3376236117035589676,50579678171158,10017891625738284,50579678171170,
    0,50579678171182,50579678175284,50579678171194]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1504 : Block 5 6 1504 1536 :=
  checked_packed [
    3376236117035589724,0,50579678175308,1211867792090341576726,
    790296414855902310,30308139797783253002,0,30308139797783253014,
    1211867792090341580852,21502496669175822,21189285172486188,0,
    30308139797783257140,9862314463246,21502496669179948,102559311415614011084814,
    0,102559311415614011084826,9862314467372,102559311415614011084838,
    102559311415614011088940,0,9862314467396,392214798667786,
    102559311415614011088964,392214798667798,0,392214798667810,
    102559311415614011088988,9177240495460366,392214798671924,0]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1536 : Block 5 6 1536 1568 :=
  checked_packed [
    24437363502913568126054,168385449415413770,9177240495464492,168385449415413782,
    0,168385449415413794,208911634276404,1191755978379274,
    168385449415417908,0,208911634276428,10561136738963482,
    168385449415417932,181701271621646,0,9326160299167754,
    790296689733809266,9326160299167766,181701271625772,0,
    1904017272519799910,11038107956678670,9326160299171892,10128602435594,
    0,10128602435606,11038107956682796,10128602435618,
    346758930129286355498086,0,10128602439732,28725434644728647702]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1568 : Block 5 6 1568 1600 :=
  checked_packed [
    846016027186705510,22420117576533151758,0,22329020175618058,
    28725434644728651828,177166457245710,22420117576533155884,0,
    28725434644728651852,91562524545046,177166457249836,33580471923190534154,
    0,5173283917838,91562524549172,5173283917850,
    1269407721773808492588,0,5173283921964,22359042367919493142,
    1269407721773808492612,9547832151248910,0,9547832151248922,
    22359042367919497268,1092563839857947840522,9547832151253036,0,
    22359042367919497292,10749817001086990,9547832151253060,10749817001087002]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1600 : Block 5 6 1600 1632 :=
  checked_packed [
    0,22742281928839182,10749817001091116,175380404952371214,
    1092563839857947844684,0,22742281928843308,9612750179274762,
    175380404952375340,9612750179274774,0,9612750179274786,
    1491505006215132356660,9612750179274798,9612750179278900,0,
    1491505006215132356684,10404539614105622,9612750179278924,45424069192668155918,
    0,45424069192668155930,10404539614109748,2684350369802,
    45424069192668160044,0,10404539614109772,2684350369826,
    45424069192668160068,91564672028686,0,10927256461381642]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1632 : Block 5 6 1632 1664 :=
  checked_packed [
    45424069192668160092,10927256461381654,91564672032812,0,
    100703736801181420237938,34071986979817394198,10927256461385780,34071986979817394210,
    0,34071986979817394222,34071986979817398324,34071986979817394234,
    170063846439318630446194,0,34071986979817398348,23333924481536102422,
    170063846439318630446218,11264703921655822,0,11264703921655834,
    23333924481536106548,11264703921655846,11264703921659948,0,
    23333924481536106572,181718451490838,11264703921659972,23568805435281418,
    0,23568805435281430,181718451494964,9991175855411210]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1664 : Block 5 6 1664 1696 :=
  checked_packed [
    39286962192862158892,0,23568805435285556,9991175855411234,
    39286962192862158916,224785833398286,0,224785833398298,
    39286962192862158940,224785833398310,224785833402412,0,
    790297514367530086,224785833398334,224785833402436,32257728353144842,
    0,32257728353144854,224785833402460,11499226315886602,
    194114928102077269816434,0,32257728353148980,10927466352650,
    194114928102077269816458,300155281776578574,0,300155281776578586,
    37574158829689511980,300155281776578598,300155281776582700,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1696 : Block 5 6 1696 1728 :=
  checked_packed [
    37574158829689512004,23788685279367190,300155281776582724,23788685279367202,
    0,28340212586942304270,23788685279371316,197647143014410,
    37574158829689512052,0,28340212586942308396,39286971160753868822,
    10927466365064,704370446350,0,704370446362,
    39286971160753872948,704370446374,704370450476,0,
    39286971160753872972,704370446398,704370450500,10381767563284490,
    0,10381767563284502,704370450524,10381767563284514,
    55158480163800358956,0,10381767563288628,874554862196309889046]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1728 : Block 5 6 1728 1760 :=
  checked_packed [
    55158480163800358980,1853551557065314318,0,1853551557065314330,
    874554862196309893172,175380482261782538,1853551557065318444,0,
    874554862196309893196,11643170198654998,24074492804341804,11643170198655010,
    0,11643170198655022,11643170198659124,11643170198655034,
    175380482261786700,0,11643170198659148,1577772643292024842,
    16584368305974800299122,24531371024191502,0,5688679993354,
    175380482261786748,11968271104348174,24531371024195628,0,
    11643170198667400,10483769546903566,11968271104352300,513679384502084883714062]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1760 : Block 5 6 1760 1792 :=
  checked_packed [
    0,4637712335933280266,10483769546907692,4637712335933280278,
    513679384502084883718188,0,10483769546907716,26451605259271802902,
    4637712335933284404,279121189203349518,0,279121189203349530,
    26451605259271807028,11460042297358,279121189203353644,0,
    26451605259271807052,25221852448165902,11460042301484,1648000316300551262222,
    0,208913781755918,25221852448170028,208913781755930,
    1648000316300551266348,0,208913781760044,12202793498578954,
    1648000316300551266372,1175012048375822,0,24876139860201482]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1792 : Block 5 6 1792 1824 :=
  checked_packed [
    55158507376713146420,24876139860201494,1175012048379948,0,
    55158507376713146444,24876139860201518,24876139860205620,175380520916488206,
    0,175380520916488218,24876139860205644,175380520916488230,
    175380520916492332,0,1175012048380020,445403673661466,
    175380520916492356,445403673661478,0,445403673661490,
    175380520916492380,10877863263735822,445403673665604,0,
    175380520916492404,11726330269718,10877863263739948,55158520983169536014,
    0,197651437981710,11726330273844,197651437981722]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1824 : Block 5 6 1824 1856 :=
  checked_packed [
    55158520983169540140,0,197651437985836,30308139952402075662,
    55158520983169540164,25645399641427982,0,10919279230717962,
    30308139952402079788,10919279230717974,25645399641432108,0,
    30308139952402079812,5946378031118,10919279230722100,13446169418010634,
    0,13446169418010646,5946378035244,13446169418010658,
    25908014389095571500,0,13446169418014772,39286998064429010966,
    25908014389095571524,39286998064429010978,0,39286998064429010990,
    39286998064429015092,39286998064429011002,5946378035316,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1856 : Block 5 6 1856 1888 :=
  checked_packed [
    39286998064429015116,12679924636717070,13446169418014844,12679924636717082,
    0,32258011820986382,12679924636721196,32258011820986394,
    768886813813746499240080498,0,32258011820990508,1726247971343260717078,
    768886813813746499240080522,11241654375682062,0,11241654375682074,
    1726247971343260721204,11241654375682086,11241654375686188,0,
    1726247971343260721228,26908177471639566,11241654375686212,1520414232586,
    0,1520414232598,26908177471643692,1372234242130263937038,
    1726247971343260721276,0,1520414236724,11321206967898122]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1888 : Block 5 6 1888 1920 :=
  checked_packed [
    1372234242130263941164,11321206967898134,0,25828749043830794,
    55158548196082327604,25828749043830806,11321206967902260,0,
    55158548196082327628,177060432178057230,25828749043834932,177060432178057242,
    0,1297389051744129912842,177060432178061356,208914855497738,
    36534135199642726,0,12258906218540,208914855497762,
    1297389051744129916980,13446311151931406,0,13446311151931418,
    1297389051744129917004,13446311151931430,13446311151935532,0,
    26336304857890952,791063840165990422,13446311151935556,29417340237982470158]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1920 : Block 5 6 1920 1952 :=
  checked_packed [
    0,29417340237982470170,791063840165994548,27288161214271498,
    29417340237982474284,0,791063840165994572,697903458816010,
    29417340237982474308,42091144854361870346,0,42091144854361870358,
    29417340237982474332,42091144854361870370,298454295949353004,0,
    42091144854361874484,224787980881942,298454295949353028,39287016000212439054,
    0,39287016000212439066,224787980886068,4294178091569162,
    39287016000212443180,0,224787980886092,2503630853120737677334,
    39287016000212443204,27066621096890382,0,32258153554907146]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1952 : Block 5 6 1952 1984 :=
  checked_packed [
    2503630853120737681460,3359343621034901245966,27066621096894508,0,
    2503630853120737681484,3359343621034901245990,3359343621034901250092,3359343621034901246002,
    0,26767422736306190,3359343621034901250116,26767422736306202,
    41751460071396786320486,0,26767422736310316,27281081027792906,
    2503630853120737681556,310064126468558862,0,310064126468558874,
    27682500399683608628,310064126468558886,310064126468562988,0,
    27682500399683608652,5189411947941910,310064126468563012,5189411947941922,
    0,11790298598346766,5189411947946036,11790298598346778]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_1984 : Block 5 6 1984 2016 :=
  checked_packed [
    1269173481312858304164978,0,11790298598350892,25280381219147616278,
    7439354574156902,27873456875900942,0,27873456875900954,
    25280381219147620404,27873456875900966,27873456875905068,0,
    25280381219147620428,4777215346610190,27873456875905092,11986222524141578,
    0,11986222524141590,4777215346614316,11986222524141602,
    43494153577241256004,0,11986222524145716,6461774106634,
    43494153577241256028,791064132223766542,0,28527946473934858,
    5135911508712930423910,224447738941454,791064132223770668,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_5_2016 : Block 5 6 2016 2017 :=
  checked_packed [
    1465060117996126344]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_0 : Block 7 30 0 32 :=
  checked_packed [
    0,1371541514,0,5498736650,
    0,197866295306,1069555764,0,
    236521005100,11089769140234,2143297580,22007517194,
    11272439472180,31507909447690,0,1495248408586,
    177746999260262,82300192690186,128979050540,2902991048714,
    37770240204868,0,42584932098092,4543333011466,
    45269253103692,120104494829578,197832745004,212865126410,
    0,139451175014410,107906867268,161583711916042]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_32 : Block 7 30 32 64 :=
  checked_packed [
    121148440322140,113804046241802,6460230606900,0,
    143761443135532,4608825415962634,305475362868,358517357678602,
    158836778344500,335540129806,0,88042639370,
    1523403202770022,181449781153826,711081336900,185182141288458,
    188987448762436,0,192542977040428,462116599369738,
    204062783971404,10499311800342,10499311804468,562583601942538,
    0,1038779622008819722,904354865196,936567115786,
    215817928840,26402482821271562,105222512708,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_64 : Block 7 30 64 96 :=
  checked_packed [
    8926191654286450,25081128423438,25081128427564,11618016563210,
    498971713749128,17175678998,0,1292226067959818,
    8926603971146854,610954907662,610954911788,12644916400138,
    744747979256934,0,600050212282412,1435480407150602,
    47168416179580823417994,1783211098300747786,628525845454900,11621237788682,
    0,57939330043220018,21421540008539238,761284089876490,
    1218181484267970652,62206519906668554,685477111799876,0,
    8247380374049535090,1486591365158,1486591369284,1721989085532170]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_96 : Block 7 30 96 128 :=
  checked_packed [
    713952744980616,57939407352631306,0,1761533184970762,
    31139410321880166,880539493994510,880539493998636,799379644485642,
    25704687554540682,0,20998627794988,851473076234,
    12225161201726602,1962079099555854,1962079099559980,2008497763913738,
    0,2474240971882106890,2001985855299660,2463204676472842,
    3263694654381498460,52805038359187466,13888980525124,0,
    55033065881220198,2168271889502230,2168271889506356,45764214525962,
    427558470431846,1087507725849464842,0,25710834474815498]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_128 : Block 7 30 128 160 :=
  checked_packed [
    32129408873542758,2229020443807766,2229020443811892,1669126963597322,
    940153400281639433354,0,2059608948482092,3263694809000316974,
    3263694809000321100,57939639280865290,34355552300,46433424117770,
    0,287728862972950351922,14472886816212005990,2463250780262426,
    2584609376190648,110423452711653386,53144456773247044,0,
    4664867176600,2287998129410094,2287998129414220,42009919381049366,
    42009919381053492,98813503082510,0,45777099427850,
    4931155148936,11124111134431383562,5064299126852,2459290015109130]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_160 : Block 7 30 160 192 :=
  checked_packed [
    4483121820601425988,0,2440159492579372,5758429750628362,
    81543639846630502,1413460603267190794,1563072275685428,116773280840421386,
    0,178321110722265747466,5463731085356,352183128074,
    515208015525002,105609975488843786,161285815672884,0,
    307254171634809970732,15991301312734040074,2661264408977484,6314593655721994,
    2661264408985736,112213801046038,0,50172864237602,
    214754768373953638,3287300922413094,3287300922417220,2832199409733642,
    84458059698549862,0,2916068376977452,3287373936857098]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_192 : Block 7 30 192 224 :=
  checked_packed [
    45357037592256588,13744522618613010442,177160014798892,6870757560815626,
    0,15991321722418630666,7026945053171756,2992921783570466,
    1381406282364018,105610091452960778,3230884962348,0,
    112425805119758380,7043300825501710,7043300825505836,82581492873564170,
    385916096734442823732,161287963152398,0,7426921465909258,
    6662026969240,510921207384683581450,7277823219736652,395531454244720650,
    7277823219744904,0,54710631407660,91543197192202,
    22420756163998822,3389014941896726,3389014941900852,236482338463158298]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_224 : Block 7 30 224 256 :=
  checked_packed [
    0,15991348935331418162,7886611412951132,1664802468401162,
    7886611412959384,105610207417077770,7327746891828,0,
    428784053990266511404,7460890873870,7460890877996,3746281033738,
    44191272764807591026,32654872486671814666,0,8646364686716978,
    364779521227344194843750,17035584336155381770,8417996980625452,440641473541574666,
    133410671730630724,0,8678823834951756,98005648146436106,
    280025215444989042,262545574404821014,262545574404825140,91549639643146,
    0,8818253572870166,8818253572874292,8126610804770]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_256 : Block 7 30 256 288 :=
  checked_packed [
    229947018833835122,105610323381194762,8653844372267052,0,
    532588275332822130,359842378079522525194,4132828094516,6575349307543602,
    8684957585129800,2063727595534,0,8526042763274,
    373535959545945273446,772979051630289752074,24446449671542415452,106621937731506186,
    30308139720473845828,0,8217801038766124,19332570810421258,
    8659186761880,38935014073935335434,8306221127835700,40953555049716387850,
    0,94671599352926177333306,253407160996738162,91556082094090,
    154395538341503068,26190893216937545738,20262711409516588,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_288 : Block 7 30 288 320 :=
  checked_packed [
    21449378861878807114866,9857569556271142,9857569556275268,20446599427657738,
    6650672682382438,9292136963769372722,0,10092091950501898,
    50496020459789542345421926,41716037696249401354,21089234915958836,50579678171146,
    3376236117035589700,0,314672046288150572,21502496669175834,
    30308139797783257164,102559311415614011084850,9862314467420,208911634272266,
    0,10561136738963470,10561136738967596,9326160299167778,
    168385449415418004,28725434644728647690,10128602439756,0,
    10128602448008,22359042367919493130,5173283921988,1092563839857947840534]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_320 : Block 7 30 320 352 :=
  checked_packed [
    1092563839857947844660,1491505006215132352522,0,10404539614105610,
    175380404952375412,2684350369814,2684350373940,34071986979817394186,
    100703736801181420237962,0,3126144555556908,181718451490826,
    10927256461394104,9991175855411222,9991175855415348,224785833398322,
    0,55158466557343961098,11499226315890740,23788685279367178,
    37574158829689512028,39286971160753868810,197647143018548,0,
    309711502187705446,874554862196309889034,1191760273350700,11643170198654986,
    175380482261786676,11643170198655046,0,11968271104348186]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_352 : Block 7 30 352 384 :=
  checked_packed [
    790298064123343974,26451605259271802890,10483769546907740,10656191411654666,
    4637712335933284476,0,208913781760068,24876139860201506,
    323787587485447282,445403673661454,445403673665580,11726330269706,
    0,197651437981734,197651437985860,300155318283800586,
    30308139952402079836,39286998064429010954,13446169418014796,0,
    13446169418023048,1726247971343260717066,26461637707833388,11241654375682098,
    2414998752080998,55158548196082323466,0,26336304857878538,
    84859165299647952467058,208914855497750,208914855501876,791063840165990410]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_384 : Block 7 30 384 416 :=
  checked_packed [
    1297389051744129917052,0,11542878819983404,224787980881930,
    42091144854361874508,2503630853120737677322,4294178091573300,3359343621034901245978,
    0,27682500399683604490,3165386711084,5189411947941898,
    356631786513511526,25280381219147616266,11790298598350916,0,
    43494153577241255980,11986222524141614,11986222524145740,28244799748313098,
    304959491375068361842,3918904627056909226034,0,320378438890295306,
    2706129262330356184166,37574158984308330530,28941208227160132,12225808282161162,
    370707871811253362,0,3153461724838874849324,13324058103842]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_416 : Block 7 30 416 448 :=
  checked_packed [
    580353232216346396326900874,116806070235054477322,28884375139524652,29358828365549578,
    0,25221852985036846,25221852985040972,13000435027677218,
    223694396908864341549148,6133729294457216438282,28255078678798428,0,
    3504762818769466482,29686022195384342,29686022195388468,331384394323333130,
    384783957108995318,2596355344833670287370,0,30472856982786058,
    3573482295505466470,122368199118420971530,36850191927615556,791064716339318794,
    47703179745879400516,0,109429588500524,38452756565987338,
    234345315262681231401036,34086704987135545354,958015922667266100,351321376155504650]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_448 : Block 7 30 448 480 :=
  checked_packed [
    0,256536379133966,256536379138092,12258421445234698,
    1629489336133456240732,97539923960055992330,7234868224052,0,
    2819673603543882806386,127930328001787465738,14655497969708,363365503340554,
    109431735992456,32660564006146062,0,598105198014100535378343628850,
    27131239633298404454,27489045561466687498,30986574799839276,1682466748181254154,
    50509197191638163580,0,11965382792736850113999986,7492566257714,
    1906556539058009190,48892899252559155222,48892899252559159348,38454431603232778,
    0,308975600049827965046794,36850475395457076,33900349265809434]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_480 : Block 7 30 480 512 :=
  checked_packed [
    51912205914517545052,87867227700417531914,63961958772121644,0,
    13054779473478557740,999302202776358958,999302202776363084,382264313420713994,
    999302202776371336,2419011049670077059122,0,15720649854986,
    33694257474715800,32807572213862422,32807572213866548,791065592512647178,
    54444449262074863684,0,1187688938043613228,34495904530567178,
    1800992732135584440396,29753398018445334,29753398018449460,378896760291987466,
    0,34738575148847118,34738575148851244,7281929409794058,
    123358136038863974,92936418170700304394,16253225803844,0]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_512 : Block 7 30 512 544 :=
  checked_packed [
    47949953945244700269098098,272411652001806,272411652005932,19434909929570308118,
    19434909929570312244,78086420606794862602,0,38456664986226738,
    145377358087281960825958,2596355357821651390474,8265660375084,26099080123912202,
    1886744430136648540228,0,35684822814826572,413207250685923338,
    35684822814834824,3904807837123066466314,36745647591792716,31499903519690778,
    0,15959999377900820238346,37633285731393628,118843492659156226082,
    37633285731401880,54444449339384270858,1104092532851089476,0,
    71064529009655960,784456981942310,784456981946436,295958648478333145098]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_544 : Block 7 30 544 576 :=
  checked_packed [
    58927249528914452532,34071168880587313162,0,30658531103346698,
    13054779589442674804,659737066416801583118,659737066416801587244,3129281170395631626,
    6173148353864379932740,0,32969309810597932,185733709041674,
    395289726828680,155740972418619936778,33325114699292724,1044355353119562659794970,
    0,156070330379395928074,36267773403228,635394504790042,
    36267773411480,13054779628097376266,822981496414260,0,
    214783237688777920118535282,37673248992792590,37673248992796716,601655764091670538,
    378717438851119086313524,38983912889782294,0,39541775454441522]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_576 : Block 7 30 576 608 :=
  checked_packed [
    378717438851119086313644,161303101301986430986,46796513698914348,6676517127983114,
    131472540441785446,0,4887668596788,79301729967247724554,
    63136275697552597068,37891271036942,37891271041068,363417042948106,
    0,697924933652518,697924933656644,34992914522181666,
    12265025209119846,108143989581548621834,81875853436264492,0,
    394495759192995372474412,166865230185352925194,39464422153920564,85015683372421154,
    13179825431190192264,1733750071055730801119242,0,635076107212689418,
    53934852270726714906129510,83480281419354134,83480281419358260,1229139944452134669389834]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_608 : Block 7 30 608 640 :=
  checked_packed [
    4097267007092321951812,0,36432489178210348,875521562906650,
    87705225179185288,36426586685181974,36426586685186100,1261278027963174938,
    0,85229648752796504074,9554475257700396,411072389451786,
    2574905540752716914,67345301866190737418,42255538662154284,0,
    28160922142208172076,37320310457897006,37320310457901132,43133879942385674,
    4233831783949053993012,17497282731076134899722,0,3902018385046671370,
    42724875508400264,4156724805334502215690,10346572030028,44318754179387402,
    68748310589070123076,0,1334468787888493436972,42668505606131746]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_640 : Block 7 30 640 672 :=
  checked_packed [
    5325927770881012910,177831598748057210890,1313673193000542260,38155225122476058,
    0,41679432192022,41679432196148,91549525541954523146,
    17932487635847094420,118282370522114166794,5368704933932,0,
    60616280035502858284,2596355377303623045130,43046768476168260,202445099838222635058,
    60616280035502858404,183551616835452407818,0,43733556698025994,
    38843155028996273254,75062859850831630370,6252289115299988,1582129269138526218,
    75062859850831634556,0,39359178275299372,885520515207178,
    8431346458550423527500,1926378642123526321999882,39983774296973364,43302929829922]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_672 : Block 7 30 672 704 :=
  checked_packed [
    0,44644055405039630,44644055405043756,46797080634593290,
    75062868818723348572,33128648648687620106,40427684936818756,0,
    10311381259444656551026,784508521549838,784508521553964,1408745082890,
    60616280074157563956,4156724811828492767242,0,216947087812167995402,
    11270313279076971622,4643526114519250112546,26074927912198236,41315506216505354,
    131472566211589234,0,1313673777116094508,46214430605709362,
    11098484121705520313518,1311099936722759293341706,44926427471948,96638734740492298,
    0,46465052819066902,46465052819071028,38199168074495561738]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_704 : Block 7 30 704 736 :=
  checked_packed [
    151528641156951842964,137715825496050110474,18104254819035258948,0,
    41612501997076664,22920088784918,22920088789044,48356917663240202,
    53069362004767882,46008759226382,0,9417096433766410,
    154334694474277462132,98643383414127857674,108388349936410676,1313674069173866506,
    5145987644222003486844,0,43091148775890988,1173789861744698,
    102010147408199816,49295591355715598,49295591355719724,229463174742427045898,
    0,784525701419054,784525701423180,101027332323545098,
    4916655668232714199132,137715879303400394762,43341140434362436,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_736 : Block 7 30 736 768 :=
  checked_packed [
    6611548630341923942,577922594010857952251914,43978970055581772,159946801108928696342,
    159946801108928700468,1059312921007426163970058,0,2824847559283970074,
    3872979420069396231270,1270769417981998,1270769417986124,30674674677452810,
    60616280151466975300,0,103604372696473652,106001911622144034,
    5053220445089446240332,108388916872089614,108388916872093740,44598694779031578,
    0,50595356437647398,50595356437651524,11087275668541474,
    5485693035750634598,277121202230963212298,822998676283436,0,
    75148318137970073644,177831598864021327882,49255754506308,222835771648983961610]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_768 : Block 7 30 768 800 :=
  checked_packed [
    75148318137970073764,105942273182666766,0,1238615029918470154,
    142832037536637378376806,2670031699141480146800650,49796920385588,1582130145311854602,
    4319655382517282780274,0,8588356187332652,10241523996168202,
    60616280190121680972,46642433894649878,46642433894654004,46642433894649938,
    0,1121625440653251889336330,103920582684319820,22292190361292810,
    87307881940474929244,12267458610324547047434,47086344534499396,0,
    6370731681769832063020,109119919392039112714,46798417308950604,109804527489650698,
    10012101377955050037300,109804527489650758,0,51420418019362]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_800 : Block 7 30 800 832 :=
  checked_packed [
    10012101377955050037420,127558997665386510,127558997665390636,47974165814185994,
    47218453030912152,0,890886271541300,232602069324099751946,
    60303049003906150,294018683156406734898,213256533809569884,26115544453130,
    0,36799516650530007945226,13331930566505804902,5355070950704418826,
    5832064362188183183452,44284971998202449367050,281446286685932363844,0,
    746856535532650361719370866,55384228329689126,55384228329693252,113625527830450210,
    33639003845531622008019760314,53043915657262,0,885533400109066,
    64259905667955597561050214,1516271528518331182092298,26648120401988,1582130583398518794]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_832 : Block 7 30 832 864 :=
  checked_packed [
    179589174330208034884,0,49749808373571628,9554526797303834,
    75148318215279485004,167989051658262,167989051662388,1263184214979776522,
    0,4156724831310464421898,54126247419948,116130047143710730,
    60616280267431092316,307536667896761552906,52964738094604356,0,
    147476957145586051593330,2928409721010287418544138,28289703386000924740,57434267759677450,
    50637629653270664,1270775860432918,0,6811813941298,
    2931044876083023671473254,116944936389054478,116944936389058604,52965296440348682,
    185201280964859273340,0,890903451410500,27713272287266]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_864 : Block 7 30 864 896 :=
  checked_packed [
    6175102721171273031756,175735462776526606386,27713272291452,6178211791974174730,
    0,119109749424787478,119109749424791604,3033714765559243063575579725858,
    75148318253934190684,50560762684958052362,1395841013129292,0,
    2997647292767715396170866,58815324157382678,58815324157386804,6115678999805956146,
    357316921129829417096,116675501682069518,0,434352722808890,
    2802108885282497163703398,32238475431095841067058,3493481088660133512224860,16903514011625964179466,
    6346621900662817955908,0,52966413131849772,135511742854729738,
    3453149528200,4156724837804454973450,3111502323639287415369419989044,7804030893978292234]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_896 : Block 7 30 896 928 :=
  checked_packed [
    0,123646682964430894,123646682964435020,24300164138029451055138,
    392140116965449539676,327813645007293779978,57914408575028,0,
    14349288893671552102,39909313584598511259658,14469740634156,9554543977173002,
    6958934883846599794,252277093408836685834,0,60992357180379186,
    459601078554884643206739046,251631957040003289098,63621325452746796,6115681267548688394,
    5326350052610260607044,0,241680421216067652,1414547858568253450,
    5326350052610260607164,61196896039044386838,61196896039044390964,135515092929220618,
    0,3186787742879094690287626,44945357921302518711650890866,261571597769052786698]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_928 : Block 7 30 928 960 :=
  checked_packed [
    53863919660239434854,337952133562559893514,378335174411279147076,0,
    963679755478819705226015858,2770174981705750,2770174981709876,1654301417798213163814934,
    1654301417798213163819060,19396915202282955477018,0,14985136705546,
    15393547853934638182,31360550896929383387146,31634765555955574781030,1582131459571847178,
    75148318331243602044,0,377988378319902482476,26741501602041866,
    63621467186675848,112044627812421654,112044627812425780,269106029474305019914,
    0,1395845308092430,1395845308096556,135518443003711498,
    6812881057323431026,175735642134360887306,131613120912171060,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_960 : Block 7 30 960 992 :=
  checked_packed [
    6861179439137452728364,1516271535609768864387082,1010602847772764,982385363934047637514,
    8795589374591906954,30908727955478,0,272781741343968858122,
    1030107228839172966994424934,62243735605262,62243735609388,9142355965775882,
    4810428095747166044168316,0,7539794883357746281854066,413686485404780335114,
    210455760820789846092,65346423226372142,65346423226376268,115542105580900378,
    0,134821976878354470,134821976878358596,7804032646324949002,
    610594070309752733788345233261164313314342002,358229110673092120586,129241951743516716,0,
    213261814138115465260,260629679487062038,260629679487066164,7773886615586]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_992 : Block 7 30 992 1024 :=
  checked_packed [
    413829833516042433650,115568843228713006,0,63867233243162,
    93506037476392711282,112438742564545437271855114,26857751093143737999452,1582131897658511370,
    28979488499727086694,0,118098104237957164,64408399122442,
    128626314295545700428,1516271537973581425152010,44190637137783169148,283991884918884929546,
    0,32107204892193166725130,67523456249372716,137885422297550906,
    108888898770812543068,218873920772766699530,132828764831752244,0,
    16630518226391938162,4035720510322648700424202,32506455793740,281263573315883018,
    38408374718477091395032638920816177399006262863532934699451790603072614,65490730881062,0,47175618603681583114]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_1024 : Block 7 30 1024 1056 :=
  checked_packed [
    5188754678275656135782,16652982605954483191025674,294146917070282796,6115688070776885258,
    221679974090092322884,0,75868129869751656492,284191538420912178,
    221679974090092323004,33039031734286,33039031738412,726846438117386,
    0,1621210373018659852302,1621210373018659856428,137489211644715208714,
    5326350106417610891356,378506087783624347658,122537061117862012,0,
    93506037596651795558,172349096458194966,172349096458199092,295202028493801000970,
    23149950496748058189876,2037140362255228687355914,0,290047468630970378,
    24564689904347528574054,108888898809467244578,2522011771347012,1582132335745175562]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_1056 : Block 7 30 1056 1088 :=
  checked_packed [
    108888898809467248764,0,144755581922582620,8254922952730,
    2215761449916985163915340,251631957155967406090,125030387612131380,150118397676359714,
    0,1033020871831199701536818,346760156112130250620548198,34104183623690,
    230098134042069180508,388644576338890461194,468171334718551236676,0,
    392140117081413656620,8535680246882504750,8535680246882508876,24516849202892810,
    8535680246882517128,19791234467458421570408458,0,726855028052018,
    110531453043980528149862560954,7718775336595177345058,69278892040268,26301427575951370,
    23921584058364139151428,0,441389934255628361772,306412172068717072394]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_7_1088 : Block 7 30 1088 1105 :=
  checked_packed [
    179530510628000777967695218881638,5637319032287818277720074,144007470962974764,128496529299214362,
    0,1226210920147884953309194,274873720884,157492709018308658,
    73652796311929369738,5115514070991109972037642,143589204096458828,0,
    2300983022406531576504364,2128243003785324661837834,2866146932459361542220,1629070282922659890,
    2866146932459361550472]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_0 : Block 11 210 0 32 :=
  checked_packed [
    0,1298753654794,98914279476,101202343759882,
    31852127597682,5807462682634,335540133932,192542977036302,
    64399658202226,1148971728769034,17175683124,0,
    9387047886271590,297920670732298,11976735998358630,20998627790862,
    1877674939138184,2203805243265001721866,971732164676,2059608948477966,
    50168569282712,2696147059609610,0,2440159492575246,
    2814596284956824,307254171634809966606,112213801050164,2916068376973326,
    1356323673355366,6528882970634,161287963156524,1000057379423768285194]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_32 : Block 11 210 32 64 :=
  checked_packed [
    17583905997599930,0,8069757408387140,8678823834947630,
    232381061626082406,18218542193184778,2063727599660,8217801038761998,
    337558364435578729755849866,20551807627406872586,2443832205428,1211867792090341576714,
    0,91562524545034,22742281928843332,23333924481536102410,
    23568805435293832,704370446386,24074492804341876,55158507376713142282,
    24876139860213944,26016742513840138,1520414236748,0,
    351939758080930954,1465060117996113930,43143051809405603427430,3153461724838874845198,
    36850050193703048,3405904875530,13856634052700,109429588496398]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_64 : Block 11 210 64 96 :=
  checked_packed [
    123526502787827381350,32247302252924938,0,818197637553676391288842,
    4777249706360968,625604287569334587441067069450,33694257474707548,139054585768520454154,
    29767732270481656,92936418170700304454,35215485968588844,35684822814822446,
    36745647591800968,0,37092833353539636,32969309810593806,
    24868627026643268710,70150828455471616010,38983912889786420,4156724798840511664138,
    4887668605160,394495759192995372470286,40847528123441220,2596355370809632493578,
    0,28160922142208167950,697929228623924,177989487952085913610,
    4671040680401843314,363442812751882,205484876906902666,39359178275295246]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_96 : Block 11 210 96 128 :=
  checked_packed [
    45071559739588904,45753126019403810,46479570278293596,0,
    19118912100075717928170598,52150938831425546,46008759230508,32653120753282077167626,
    10960242767732683890,193525016620286611466,104842558080819268,103604372696469526,
    10257793155946697881074690216314258916684215628938,448899508604938,0,8588356187328526,
    4319655382517282780514,6370731681769832058894,651099095260929877033806214258,8576582208768972951562,
    213256533809578136,448903803572250,53043915661388,49749808373567502,
    4319655383960391791934,0,1270775860437044,890903451406374,
    6958931997628576870,56290910933002,116675501682073644,15649001272998675615754]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_128 : Block 11 210 128 160 :=
  checked_packed [
    216265971078979771846800747541762,127560415004594210,120319764252860468,1516271533245956303622154,
    0,29843576066074,9025415199485599812,2720897771016015581194,
    242009456052661627689809444090982,6861179439137452724238,30908727959604,269026423564868259890,
    65346423226384520,27757584698052618,115568843228717132,0,
    44190637137783177400,28903659408461874,65490730885188,75868129869751652366,
    81634089978836106,143688993232392202,138541077106794588,144755581922578494,
    1738760715891972093346067570,7804034398671605770,0,441389934255628357646,
    179530510628000777967695218881758,726859323019274,311776350144831532,131280755539054606]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_160 : Block 11 210 160 192 :=
  checked_packed [
    8102873929284072586,1755941122836258623498,311468930881298484,45572536507116931780618,
    37318966657160,0,9775341379628,321098900393955374,
    18862154513407461569638,255352613897999749134,340578949513879620,1395858192994342,
    7263717365568971486310,333966945206407178,345505432829173852,3489501538614763486973962,
    0,340358839419277346,1569022952874052,63115455316810673426446,
    172354121569943688,172586839943680010,82276536819788,32107205055470643449866,
    2680464780276105491594,7651770638078857351008270,1645990645866548,0,
    804214217389170,878408854671370,374114330112696396,157511838802645006]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_192 : Block 11 210 192 224 :=
  checked_packed [
    174983702814687824,189746882619117618,180239588109852740,7046619485927527701024778,
    375668727632380056,4577999416455073802,0,89852859125822,
    40302675958545003634,792189980904492371978,3833480188008020844636,385745980005290022,
    748829334894035080,395454212412018698,401858156826730588,397616825133783060490,
    217129416130573414,0,23785524699204,2627348704952061966,
    413016138264363144,21182509908305645578,1645999235801132,37816732390222968771317770,
    3083209060405769588,162352346927418314762,3266673201127572,295223597875123591017664522,
    0,3514870771224586,4351359333840908722244,183742922066235406]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_224 : Block 11 210 224 256 :=
  checked_packed [
    10735498399042496377970,679072762980533800974,433448544708337780,99482971789044895191054,
    470554129219993752,65950747695714083541006,3549735705124908,0,
    205892832549004712790057825382,105005503746082,1781804222652468,447615716196093990,
    106087835517080,456941479617630218,266552803987759838310,6451236835257780921176074,
    15121675304470331768,4351359333877415940106,0,794339071199239489982534,
    266552826527748207754,3813666657186057195360270,3549804424601676,215695980786911923899732006,
    3098275969576744122,473933901396447266,474232614224404532,4012433231067808802973683722,
    503234268147761304,0,6906303225948,420215746845478926]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_256 : Block 11 210 256 288 :=
  checked_packed [
    103716507162393982054,46175418510617947574112266,1032204198978002996,6829651340164604104754,
    496274286797930632,102581621797949450,1944848861839237196,5317335812843738929041418,
    0,5456113504127815690,59687156326452,24670180443185695044931598,
    1765198387065695313588139122,2866013718428940130987819868287951441930,2021207578779740,868747862609934,
    2037352645300589087721819755552642699548943802507047943116575998484690022,15366178296918210068353038,1094127182025859220,0,
    502699322454851720,139601881725796456861710,61071264861252498546,62912049595466207530586122,
    12687844730097120574,1106075325776214888458,6184214152093748,15547777421350,
    455271201195966616,52063003536789514,0,78296751390934081474570]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_288 : Block 11 210 288 320 :=
  checked_packed [
    310217236429238062560478,1015423907766072250378,117443590976805287026,33004953765157810054866407434,
    360166931960011175014,5365399706625932198416398,132063797714988,73570081373424566931466,
    119731438279207171258,0,25045251368952673393980518,69074549860716461718245386,
    545767880109605048,117030369731022858,1207652650946928684,498183097502666766,
    19725206768190249514098,68208371437618,5044055222263876,12213255587551398418452490,
    0,931619175760348057614,2290826692488339500,755976777264644755470,
    1158892119581390271573231940854,2324614524733466087434,582047518251032628,52602863477592134,
    64260755670305879178,742934848737290,608261037111648428,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_320 : Block 11 210 320 352 :=
  checked_packed [
    11599396387855561153736357050,1263017998212076146698,52435101946034009190,1828624610117986291726,
    867864891757099496550,595816929730498586,3138075437834412,74637937479742,
    340117163197872485514,15608075625741422602,0,409288470289738480226314,
    5916218930249912,730821033224835082,616190059451785260,548848208374140942,
    1866656920702663275658,2444558869780745949194,231137692769853492,2937294747334736875534,
    1094267262736141399142,0,5540484722204748,9976139594560013921685514,
    918903693752880084214,6343796855081927398395918,638062438104703044,648481725432729622,
    6184224889520280,20614058692201943050,645353230989008972,7364712567783004036927498]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_352 : Block 11 210 352 384 :=
  checked_packed [
    0,525271302207279468554,1340807549695303748,38748205806066365267709966,
    645665752904857867531378,55338094711760813559878,659934816757620828,1486472045083496494,
    11875527360897842586016822698,1419960670647937404938,146422990140562486458,0,
    1428564810286514312,1099983450946890895374,3138101207638140,357297764561850382,
    1643580899897379127425335000315018,21420288515281784842,1417253311685337140,3127931696759428052185780234,
    688620772867981560,16480798509537169418,0,194903432431928952754186,
    151359446606141207654,10993585867803144612745230,1463145004091318324,78296751546789854711818,
    360167102659191387250,2896359510249482,344750578212956,630198415933837326]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_384 : Block 11 210 384 416 :=
  checked_packed [
    18769003648753209647838394,0,7887896323073800937516,61286397854897947365347338,
    164304027407242769510,7783307517366298,1530592823554875516,1497463372126359598,
    389560451925774448997562,49372753336343728186,355659795144756,923619800092792365397315594,
    0,14518141687585629146189838,1524200058940039212,41363194177916942,
    67103772106311765865586,4311918850166306420681523203862958090,101307018707600627205517882470,3220657574374281254,
    743778934927147192,150127632226391439708210,3138126977441868,0,
    41252166623446464124,641343289263741493841930,1609947944985829444,535448961060032221286414,
    27163691690218647217300845742,1581270797719179274,6533343722086492,682694083205926926]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_416 : Block 11 210 416 448 :=
  checked_packed [
    189471946965004596338,12486425217782203289610,0,1604410119381061670,
    47571053592712,1320666703785000962101258,190529040031788,4831116725305718345742,
    3374149246868936209510,1997017798657337181868042,3138139862343732,16430498599940665047519254,
    180654285192840229934871738,0,12163343196348,409288470861209648762890,
    54145753103728656520,59588226574032334189760526,174645376649181279346,4918391943448311631886,
    812620944395747480,810629867350528010,57327462387873226796,17447507833481524661981194,
    0,4741067171746725481272920936397410314,1608858185215516724,48276451063578151675236366,
    317464594211140616398330410098,401478506254346,153007098593026140,3105170501572017539518474]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_448 : Block 11 210 448 480 :=
  checked_packed [
    2008815292283973809254,5477169485995119842559004686,1637579490517327940,0,
    2008815314823962178674,845448788188336138,1651940143168233548,72433853331835153710845962,
    476474013498882043966908,158090741492589250220046,11080908782182516,1802855039581032470,
    2008815359903938917514,7792262792613898,0,173364695430860814,
    59819255567361574769467400623831799394523868397195251866683141380912302,14189396635425121241141262,210011011686468,908082973108953157646,
    421115096744168,6940774749194686490,808872385051272318539538484,18714211257686716313614946314,
    39025244007066121380312202,0,1723743406422761588,64951613454086044383186958,
    1664731638487852502042617757840486,1825327950627606538,1738104059073667196,787685417750106126]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_480 : Block 11 210 480 512 :=
  checked_packed [
    703477475703974842165379640,214476955774621436612618,889101945787129924,19192258582124900076490762,
    0,31847693202583311035142154,835834191440829236360781892,1224682367959793418637326,
    20264337557689588528242,3480544968876817911818,797574905188320941862559788,5548951633083735478286,
    11158911293866136,21420295816726188082,915209091192725580,0,
    65857272947752842342,5792374353563698,1881153025007951940,1311961918521761541650386954,
    921423464475148424,157735521960018841610,2195126020745469996,305076330259189427444125710,
    132451050094527005000,18230231148414365601802,0,80653297374567360458919986,
    955016637237726032998,5792391533432842,229492983341148,417963919088620968873994]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_512 : Block 11 210 512 544 :=
  checked_packed [
    46455537488969690054145138,15983013192011858,123026751731458337939548,944150374116233238,
    11080930257027208,0,1978627672594456652,11374616551689843380238,
    2624344063285469537205036790886,137264722996046598170,117244013060148,88983844143984745417543690,
    955016671047708587122,193163049140490250,473479338008700,3033652834966019496672526698811402,
    0,2145803665632399410,4232177416883150900,366722465642811771066519562,
    17579761048962934694229094,1939153196186341402,978473003966799916,225048287854951167407689738,
    11443877247297989394568,1953513848837247010,23482796500590740,0,
    8022640811851960,418139846612094986,49717333361497743484,1966838112189419566]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_544 : Block 11 210 544 576 :=
  checked_packed [
    1781697322148511626342,193163051287973938,36112732918567149620,6179511322719159324686,
    493115928494216,120859142121723006986,0,123768665288490832968368001034,
    1974180068137512055118492371624408418,7249885210381472445239310,2090078925983064116,2099532420389802022,
    482366648384356006994298464142111882,2126995771646545930,146892068799085813812,147444136692158478,
    2038934528089124207867138,0,11080947436888132,93956101790828506980028426,
    1138624941684879010051174,92650058950772546743570446,2150187224950382636,778280747517262723813446,
    228382138286966060206,1663370062886699484284194826,2195129370819960948,49425331302124626536805961738,
    0,257633609060362,4583112872447451180,5943175873103392673806]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_576 : Block 11 210 576 608 :=
  checked_packed [
    795546117925227850889821165442839798,20049347225685432733706,8542351561198673988,79071527088070284644716558,
    1847412087498496554158,2201023752664256522,2194541876470620204,0,
    51438643054301429992,3759228935642210635786,16972092620677172,5874589496258280296462,
    23482813680468120,4398380860463497875490,2226997739319730268,49960483474100542760816650,
    8133200548804423598232,18230235613393647046666,0,1631247489152250286094,
    66125312311528,4133044808784286317916721166,12714349189521148485684,114383180639250522231017482,
    6012863078883367463016860775796,2112412470137845714994,2359187481473065012,32455707134233619147526154,
    4465856971160961176,0,2231320457473171580,2723868964030517294]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_608 : Block 11 210 608 640 :=
  checked_packed [
    2422159399350679123058,1326318511577078995881994,6245116178458037270695916646,4230710175894058569742,
    20098021358321800,31489207940785605972042,22075939697467436,11695098755072403705926,
    0,3755294158344861438185482,77322713118602183057476,134665906258527550970007566,
    2681502232920540795909234,2323362628828663818,2301323749191852204,742624756725903697907722,
    533027900972595812194811147756,1852793334657164775434,2331362268349997204,0,
    2369852724935147656,1569958416159195795466,41169673998077070942324,192217030594862873822766305290,
    323077770984661069686912186,373410880357851073613838,2422159601660818633830,679588500124127675289650,
    232278715639680247776763982950,230333371962626058,0,290142216523822]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_640 : Block 11 210 640 672 :=
  checked_packed [
    367890078705719451035126413518028964639966,2362835626644428889494917134,3193558434145760195698,294968932631464982846902282,
    21647685188919800046302346,51961813570424858,2337227708020301868,312179960851482869130858566,
    400804086942424205636794,0,2378631016123211828,208792914287923270,
    79038056515890871832953238666,39068531338780562427930,2527042809085567052,1763409595615820158822485331978,
    2348311704737166558,24175862640352441650909198,2384372153668608068,6766523067141655667675146,
    0,2503093887833214986,2671588696616083500,772482824756671811598,
    28146444639489138639032,2517478179984117810,5245297582594334772,1875067728384245528268814,
    5238306835991117960,5116948074048000010,18813613890887762321484,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_672 : Block 11 210 672 704 :=
  checked_packed [
    3573858225420800898222,413144989236896144035854,784913423963010162,128853341631543762608984074,
    97324030179786738349111477548134,19907514205229509775410,307459524665388,1112624750707311928217178126,
    8191970875337675088247322213272764829711895653320972596357063783562,3557885097671600902154,0,235331952012242911760398,
    22076042776690840,427515286430683146,5186322323648553052,107220103451507691534,
    3287887228462027519114,68962502147632533530,2521440770901155908,15111957035503507738694,
    2513579302222577800,0,2554624979673030700,3746252314343347211735078,
    3746252314343347211747576,5489236606722248738,5404385924312211508,4043192675288530963862588289394380115978,
    2542300607524389016,11562560910266378,175222234127026626612,26338758020630358998695022602]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_704 : Block 11 210 704 736 :=
  checked_packed [
    0,193661740101375904098291726,5338094098383380548,6783167098911386696102114389659658,
    2723902207077400712,51760332216653328792162318,7949401080020869164,47163304921773641742,
    2348318301806933310,1282686581564648378601482,2659686061130653764,0,
    4601541069589392143474,126152984968997932124606478,6160785001496453212,2348600171534749710,
    3829104572153185973362,551541998977290290,82772605542468,26615348425434435948614,
    9327990550148178523238,120859189744320385034,0,231171876260352358615093258,
    8783021345646013194305263986816114,973091082019880422084618,730179422609583468510384764018,563180936172988972780228618,
    2725350819686793352,2650634289107963914,143938032941151270477876,8163747824828988526606]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_736 : Block 11 210 736 768 :=
  checked_packed [
    9480077047991829017738,0,5642336954293952564,664716736277543980634126,
    69475083312363113036133478,2805164023002173450,2712748499937534028,666133135821518077348024330,
    15775792652245318779016,750342551720403759271950,436311443972094474024137842,6854325955454029172576266,
    0,898266455116612016017422,12714349194778188456084,4141342370976784813387673505802,
    146892074932299120776,18926855418563316944906,1027396591901745268,1544577227443635667079182,
    5776031727075999896,1352325767993249406914610,12503789034545228,0,
    4882122000410154644654,479155246817294468901769226,5895631914122879092,2824287900684783638,
    689501160620216,5792752310685706,4966204923176820780,1224536306839719982]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_768 : Block 11 210 768 800 :=
  checked_packed [
    7003286970225043031791255880,45950122447871907205130,0,2088417450316032215355406,
    1330252731841906102885168242,44997004121475628457267214,390978902534345728092,50162284777869831835686,
    50162284777869831848184,657951538770094539673670,15566615038926900,2015827252654689698713614,
    26317046035504548820487921218746,0,2894016454217179180,2556967589322428430,
    2502822740542925845606,29302964148906921824266,382460746054271770740,214622735516663859619303438,
    6016682318083670264,22349348588395836739594,354581595676880104600750,43581548027358799846543724554,
    0,1326318512901853068398602,6057812373522096244,252747917540002726179508234,
    115726789945659867807880,6093549007806664714,2971593664272277580,159683644813020762126]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_800 : Block 11 210 800 832 :=
  checked_packed [
    1524126310039960958174,1754532158779095276064778,6024670539971305636,0,
    6071657676268388584,6204238372383232026,23797465167637258316,1219911727361257505820682,
    81682846880873765949553806830865495214,1583391001805679591690250,183360739614836,9258003103401286696906677817354,
    6203854999978524808,3054189201223323658,0,1728615253862523122749450,
    46210133928671650529656,47553651954763988314624014,203878064610915393612,8314174479789977505806,
    6342219177587130504,6214957869469536266,53387619539957189713972,1948177249348126848487157260702473191287897275985786048582,
    26299594658400974010,0,146892077268761321660,315587335105328744524419082,
    3094407968620298392,187621347168266,5331051489723374646458,1141453427048299457511690250]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_832 : Block 11 210 832 864 :=
  checked_packed [
    47157935812936479882,40623783809000673378,3085769976431255604,5874589498448713617422,
    0,165929993740809670666,6320403501092446284,240527619196641694145581066,
    5845057755672019317851943564489974,416070147351553448611854,6325825950185431156,2372260688061790792192014,
    6375201225738043576,1333503191705411955724358,3090395697145454684,0,
    5947791823386821745721480,6488839861947076658,6666841889540415540,768047522517014,
    7575335393495629960,3136573119632773146,6205696398621417516,37373847543256071540750,
    5499400048215832147082,51194419213100157767690,0,967126635476675770990989322,
    2707446475006714852466,14059558796267530,6476403655292493916,12043342863773158539792394]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_864 : Block 11 210 864 896 :=
  checked_packed [
    34923446399878790813780872803466,1282686583699006606544906,124621757907185906491460,3207794945112936486,
    3071124966699931022438,0,6320599486892613708,335576115804714537302022426634,
    370375224295449949366137958,394046065348642,26674206309621812,12498170682576093950513166,
    789865956393112,742303763549908604293190,6378051031028211804,2871028847443185678,
    0,635410276377386708635658,6626981360399556676,39415553146786452614200430606,
    3227721950675615880,70373912183092285450,3988311062922743788682,3212722533308567614,
    58426823089401572114616,299241179768539081347082,113988190392656880214092,0,
    2812163981402676671662,6809943203207188490,138139477167537620263036,222981951600174567446]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_896 : Block 11 210 896 928 :=
  checked_packed [
    3475082445827214423154,38715095489244523663370,6826935877583773764,26543186220362502166,
    3321319685365973128,8342253438465610878986,0,344527657812254782310584330,
    4166659943259705985193751774,52666947621340708029337614,356173649087332050660237356,860099856793261112823822,
    3321321901569097880,249525702014465891805171726,201944296044483321908,346729396771491854,
    1474036064118050831140393071802,0,6636582979638403236,3058360820756475006685198,
    44151839670681832,3414830784526159882,7392482326640336940,3399548467327012910,
    5910918746752950482034,201944296336541093962,6952361553052049460,192315967778613891142,
    0,7070149941565329418,3447663163804229676,13170077393278122732818446]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_928 : Block 11 210 928 960 :=
  checked_packed [
    1500358129806994050336522515570,3551453388329717810,1075618525398708430845150,4908134886254673090849017866,
    420022027567240,3451844882476306442,842230197657644,0,
    4504239362805187680944360,3450605275323568162,7949449836489613364,21186925978646160085006,
    1524126390854065599626,8623899668601204903946,7575344327027597404,191938640669052942,
    8536940740266059379934,61220603710164757909514,0,2901369602886822812192782,
    3504141297625612472,31682946557696075108362,7163014237038583852,28068586805209862206,
    6116678096021509649510,525817879148300865570,7209945986779586612,1219911727932728674357258,
    6898936112601907448,0,3575675203214123132,713986856294813710]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_960 : Block 11 210 960 992 :=
  checked_packed [
    43992203769541554128546915431526,375508487863764258866,3556437712774897812,2488277680114442126233614,
    3529050801601265800,82951426940893925386,3595408870555525212,5504970793108534362499977226,
    0,6943314623241880117646551158798,85089878798245940,226772314314724334073024526,
    5233027201801863326348402,7067469560655384650,4689503337000463660753012,967126636041289285505126410,
    6887652296074542986342,1188381377487333689762254858,881503378612292,0,
    4769815758694867072463986,80930358352196669450,15452384943195299884,8703384546848614125582,
    9609910610537133922858242,7426330092021747746,3621529902932566132,1866903439683259593658378,
    3605369147883536536,30929307719176202,0,243813569021470963214061666]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_992 : Block 11 210 992 1024 :=
  checked_packed [
    693744058890192468961197034503655030643940620760398627763563045818967536778,68887607112646038392842,1462934917329895617999986,1235727595198617590920384522,
    7495446938863550600,3639700711266062394,11117177932823409778,317476041378953828872753162,
    1593227925518562939515131337389158,0,9086397515909046324,6922981544562758,
    687763186125383972178375782,1025618053947627409434,3171161080960842216586,11149086556164110,
    8036724562634328785144,698631174561051495632910,3759570766945853492,6066546116008161768203677077514,
    0,7636982776008282138,3262845215927938942930788404,2449364758459747412217870,
    3988311239944115860594,1282686585833364834488330,775520395002091917025348,388627197175189697032359986,
    458985970876600,1573674742718664714,182680346838865813580,0]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1024 : Block 11 210 1024 1056 :=
  checked_packed [
    4506651710155081813629875374,1581816940123394098,7704655404931752004,1630793696916281923473418,
    3798631146059922264834232,3144022456035517800397148170,3747550717255098412,1421049563852821918002450442,
    29850148809791099650200,66237436199673647861770,0,52765497336409018601494,
    7853629839817851032,48275529100704804010725390,7842328381508034652,6783036463069007886,
    11580371395279860922,2295224193645735787368462,1062892124850861645876,31966149868523542,
    8898000641364869256,0,7894620749992829004,1103632336888538186681159694,
    135392643835489530426470,1718699011747016840581190,8022103909814247492,23709172797982476603406,
    279819371302419799433822614630,215663992677960536503409097538917233221355410821130,323785405310013616605134481749193830,1379988561732939952618697920522]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1056 : Block 11 210 1056 1088 :=
  checked_packed [
    0,11073110212950192992292874,7994100156242862148,6959487958998690867976343566,
    7981897852165046408,8027521548275421194,1206628767116566572,266953692495610908718,
    7507540223844746802290,1476309628064526457901070,7696946533756837940,0,
    40196002992373912,3988189975723118602,120968327498112066549462118,478572328093036350919858458634,
    11940632977190433894,16630053741241504370698,7753947278125047876,3462982383745714190553102,
    5800016424936169436886190,241718338533313220618,0,47123493731644609662990,
    453108694868270649110563927394,5467892861936412137623562,3948684781708910644,4159209364072569235312654,
    3988311332303092593802,977504487608330,7836858837024907356,2968358965474056187416646]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1088 : Block 11 210 1088 1120 :=
  checked_packed [
    3475083257266795721986,0,8536940835098937275494,138642442762990703888637628426,
    83984234167691866953410932651110,9886726352181412883337226,42710598433120300,1487927028612435067652997648434,
    4883306147579367637609624858,76084806329133921472522,7924949511229677684,299342227912453433356980238,
    0,1698935544324558858,141016293562561127784516,2059414143407357016674314,
    4672347272447773393419256040,22887754498941349007386,8449927182716772404,24970296207650634862606,
    25492123495377661867110,13304182756034374258397194,8333528684946268236,0,
    1747058989841814703277346725573818,320907437229542247902482446,270741669657438068780,331978226629077403455983626,
    8101597355096162456,228753425759570858080834039292065323442478224773130,18972291379849653570819334196,1235727595795233490872569866]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1120 : Block 11 210 1120 1152 :=
  checked_packed [
    4836520012873736402022,5359684198315379107303434,0,82586137986404727132230,
    345192704789831468933385545492477042,82059061587679379988680718,62978415876332832432220,8610360910055215150,
    6954878847855109731760775995864202,1016777668562978,8484106390053330996,215242091067946824315703306,
    4183994694566428808,0,8663838819168034860,360628123938254564001583114,
    97470475925552883131447395759290,1638013705526500448874270730,29302088042511090070630,42710607023050774,
    42710607023063272,8631709441210716170,8528076920636579884,16668399977038018000883552306,
    0,1884495460615989314004717582,238821510654703182036,255206861540459226526126094,
    288814068913072181887112,1527473951314284554,8724504363432681564,17352664353508153177935886]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1152 : Block 11 210 1152 1184 :=
  checked_packed [
    16742478678855054089361834168,1377450794006475706418,25428698388498678292604,0,
    43349777399238486139441525862,8386603893093568538,8471644740012482604,1866903440254730762194954,
    5224178615947637874,6813235746904993346000785418,7293506786003689629512905842,3248465200536126337492979726,
    8735069231898443928,819921787637731338,0,7616772078594691086,
    1773223581275171830699985331706729127546467502,1327585318458026625077258,44152028649234500,40196088891707414,
    8265181024452773688542,383835962909700826796658702,27768020299509224276243594,17331347693932359294138716170,
    2456701361926457178207550,0,8794546312407162932,318497300509640135502991406,
    697725700777381863373157478,17038161565716490,8900898879927492796,853746163161464049726]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1184 : Block 11 210 1184 1216 :=
  checked_packed [
    37531583479950065284282,1827766008945840178,8653788469128077380,5207628173554266365274468913162,
    0,2620018161806477793169422,132250628792364,202216321393440520964935690,
    6954878847855135575141671103378546,532701914122561239348416526,49917031180410996,533580619318922566547252711474,
    8898715740400533640,1415405051256003247476750,8796135363333595228,0,
    22587414523741979753333160,4350598001598589355092348938,42681965944954347855996,27381673045812556699616253216559114,
    8494769145849145472102,10497616792877710497026098,18363716935893393452,6986969375340008065697058826,
    19047120404475034798288552088,144343458238674950426634,0,1482794101876145151302176782,
    9252095819409015016,23125042367827978,25007516869992540,4140249404786801119246]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1216 : Block 11 210 1216 1248 :=
  checked_packed [
    2174339532310248732635689595712614,326552146341162543294189638,9077596341672091716,27492543026986951381006,
    3988311517021046060218,0,72274607867512758316,1698117115146631904403394610,
    6954878847855148496832118657135718,9093927941598167485858713610,2245112583259127633273537136499292229643285618,11176274075059144888334,
    96507388097285958068614282,89633743930435892787810318,270741672285958053956,2145794573789346462849837305866,
    0,2096491665371457751355462,554231165624388,536122771555044163118436366,
    13301898483985650040968,7610010502881704153098,8996016146129887308,12611086729318093557774,
    11222207457734403373692052364604530,2968196737536248053239822,9119484553193332788,0,
    18931621563587379352,103590926843289538570,9280581055457271900,107306861296767169728526]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1248 : Block 11 210 1248 1280 :=
  checked_packed [
    19187774274517111633164432545183284,33744143465753159405578,9327485095948329028,788330078010200240169169195018,
    2486398876707911976858153344054374,227314443608895000586,0,1321454475949334229600440334,
    162114700327543537415390,825223961964167965013956366406,19282030417506476180,326832128587450028054,
    326832128587450040552,9407349745455730698,9391235445712494668,1063193667784675342,
    388007303749467173589887672979043466,0,9532856931887095972,3794103686619017790986653766,
    2649354304122206266864742,2125713141687400023428435982,9221902465740316716,299089334584274169219948474273802,
    25428698390543082733720,4272411578262529771430744074,9250628237808115764,28753666436655109640206,
    0,603826363767870984202,9449396244641226796,11886351867656385073166]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1280 : Block 11 210 1280 1312 :=
  checked_packed [
    448978273745286908805220676722,3381166124282826039758858,9308079781943713860,489229271346884971241410570,
    19831816726736027944,573678983742571775048814606,1821084853383209036,0,
    33154952840040033563786,36659794295294288465930,107367280383369268,13319070809812354732046,
    3958476931868465466234123378,154332611943792690335794,9394257098147111004,8450507694120374286,
    178033195817234589565080,154832069629048577331210,0,744132325645777676124819466,
    2723463773996878574258844881400970,9840085227081306122,2696867687272191562364018,56873139920033147785230,
    4487802296847053108338,285648259440264240697354,307388686759984101335092,91790009805486070580645902,
    10192036851640975512,0,9509160186418307196,4527345704387502673966]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1312 : Block 11 210 1312 1344 :=
  checked_packed [
    328474106994810979220468838,10435878410221644899313258506,20142776223363244100,53648888648800107586201325618,
    9518933194179625096,1140296004266773284718120974,103924939257552940,24237974930079500962023608390,
    0,808779267218708109723701258,25428698391419256053804,2368473385461194813094236170,
    9539723347374391448,9998911479291580426,21552304348509706420838474020,8638447670312046606,
    5533587366634368021690,24609788939735090,9832928234239434804,0,
    19983292948933525736,772970594723818785057357989919975649841166,2409515303575628,20635754202759434302,
    15646948960591950986,2814894542918152397787150,22644311703473383844398243916,11550959478178320422,
    10106417603086925976,12438096436006922,0,769187285935023290643910706]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1344 : Block 11 210 1344 1376 :=
  checked_packed [
    27490016168181594054597566017373746758,2652637025090133227999242,238390682717773635676,14835745052841958445126,
    9910727176768100284535682222,38312022546837871267890,49093276317261868,14040681377438493577230,
    26615801918447512649066050761986,0,29704322235191610522900378762,18262187820085209190757618588634060951562,
    11042640655626451731069049862370406,9853869451231891466,10126893271260078172,518169594053811009027575818,
    809349699091018574776621872230,53348369136881714,6956560504629206026564782,3089154455948080680275982,
    0,460885035398241206560362510,9958557614772068524,2756623090742602128743731210,
    11042640655626456373993293146502258,9940046767435288610,307388686831452357140596,4500924651947993886581854222,
    20585710147111764152,10272588998979358730,26297326200734450937604612140,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1376 : Block 11 210 1376 1408 :=
  checked_packed [
    20690862188744742497435880,614656053362582310749212686,275173905315708018740,2780387082752218179854929970,
    10046670981704990856,9005730519937191946,49917512216748204,9976976308485230654,
    35842385704598098285418263726,165320681019422204235786,0,31275913255991426158606,
    2505894369706136,2652637025247844427108402,10343440209315635244,796594482787813644207919114,
    11042640655626465659841779714765962,39579404055900223180810,21788046839596982340,11550968342990819350,
    32017717696812359365734,0,2732828253922065915996,2381267692270052938159755274,
    6956560504629687062901862,1382810815646492861745074190,22039462210739118196,29470449335001863426150450,
    49093284907204984,21407599983526416394,21174035247011995772,48436481994682103937672155146]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1408 : Block 11 210 1408 1440 :=
  checked_packed [
    0,103160145502011857571850,4047319903957426244,40796817684200273641077848674318,
    18005915031805458658418,88132516308848666,49629808771821710881894,61747963014227416846350,
    405957563691409531857810534,3805867342993875745640458,20690862189382596680491084,0,
    20526798706939806102666,10597323005212233738,21975649996131803228,107637302411449602062,
    25428698393171602718968,2157562349785976882,49629808838891920176266,27730349599253148404289582,
    10477551150604238984,562125116161036128266,0,3942266551433670062369673226,
    31413921951140163481002587238,213253063892550272684090,10599992213435850820,35864823185282315073489997834,
    26874725562010583224,2193881497331568650,76554994366582540027830324,2575714805323511585979764746]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1440 : Block 11 210 1440 1472 :=
  checked_packed [
    11042640655626484231538752851293370,0,28947981173551690533832761420,32537036665659584417806,
    165545215279240,21690141677105188890,2611035169103916,53348382021783614,
    5533587505172833121394,1593739063406948597423411270,154052587585282100,199506804662426218334567534602,
    0,796992548965614224739930126,18444001416257917170802,51418825681067315214,
    9462206173426952706208882,4032863290454657835470862,20395168715212880617524,44043530363501390920383135978885170,
    10865392627709132936,245800789657804982980618,10954656470620184620,0,
    1375791765756106068367258978,11077231864996433970,107479069921756022060146,26821013428654944817222,
    5533587528262577304678,23125763922333706,10713950278039642300,319367283772810596366]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1472 : Block 11 210 1472 1504 :=
  checked_packed [
    1259964168696974928383063214,1997858364739438887898940706826,0,15086318633792819423972692070450,
    53348386316763272,1624685264463604679410978830,10660985240903753772,13714214599300925624334,
    18870198514125572682890,3381166124945213076017162,25007688668684340,849363158860609257105002506,
    33043614624676590706,0,10983524203034058828,582825941613416462,
    561155332963036048176370346071438834,7051269836136770659422234,6484828119290093636,2439333522482104854999207946,
    1606240359384726659678360,128678998525458430038066,4845404539194449996,419940292344344861541820010546,
    0,34200838547436976402862090,10919966458930798708,2434987744075466743727788046,
    9401836101695537208636530,11133464225085657098,10831987474008383580,26863675086534667527390989635233014353930]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1504 : Block 11 210 1504 1536 :=
  checked_packed [
    237193956521744279474812078,11220642331751354418,22906953957445214276,0,
    4047319908252401896,9274675157385649065994,2724937701793964,490459842170971402639209270349834,
    3749051436395742032829733680266,62765079557849183047127050,10902014955653963892,19204445694576631118037498869059598,
    452157763383669568650,11344908883593269258,0,2544038155312792049322823690,
    33337221631582285558867571826,146837494780389523785718435854,3670898085366916795898378058463196262,23401123598334693398,
    11060351878079463560,4440249118500023263301738,11125982639821955116,69060431151664975581198,
    3148306063151392981267642,0,11015539256343928980,4217308402195380423272435722,
    9462206185787662425666662,23353231301169647626,31551585313070845534260,199506804662451432335215693874]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1536 : Block 11 210 1536 1568 :=
  checked_packed [
    11042640655626521374932699124348186,34064339842406479655079994,11104194215700078756,4182150454525391739915503407114,
    0,52565085416259830898595417208990638050663791002136875018,229408588285773690708036,2586529016370701307626917902,
    92420267863295525929096,23574027329425379362,1396457072500788,2381267692962675994426085386,
    11232706510486257848,1924294443072185438218,388425345413524966350924,0,
    39948161825156854985830,5802224745475200555945994,397196096583196204867708,2782956225185828358865293322,
    49629809576664222413938,85855934985741189255178,23932905970521350220,64276436359785750728718,
    401234819069742797570200,2035816354230517225733754890,0,2821316767911974,
    284165816030740968951633695224934,11287993428954058762,23497393271639908444,4323034970389873692686]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1568 : Block 11 210 1568 1600 :=
  checked_packed [
    34896467639339595010,4357878382001944000466958,809349699111953715974128022666,14646954189620704593317902,
    2441482917113774312,0,23702081859617824844,901978575468025047595094026,
    20094600114079067550822,135920669874847311990794,11448874305337696308,44347146449138101145047054,
    23944744502143500472,1228033439281176383498,133778454897736961499284,1027864140456631734286,
    0,90485816685683850350602,1103084061846413380,688574734947424139797860366,
    46965772857131240,105979197960008002179082,718822902341708,9072213119937239834750886088714,
    49629809777874850297054,88312864599097487659058,20526801862538177819786,0,
    11706278072071241880,2882648900898826,72667582699075752242795930076591206,97806040011116590]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1600 : Block 11 210 1600 1632 :=
  checked_packed [
    35617021589486318766,2419964896333527052254820962314,24123422961718796356,127010636596358613569606,
    49629809844945059591426,371278920813750641496074,0,32101398538611055399014414,
    8922453649745319781110168076347782498,107321506549867049127986,24720763748802895924,13600702130335772912455132385290,
    26874800912916824216,11835617748015124490,11924920904775114924,3255666922944539202078904330,
    20598765478765800731834,0,67315872784388657116094580,881082818860482794239299598,
    366721483423976,84533467580687664025610,11900287585987076140,14040681385942528823310,
    123542149305768635362519411602534,2591026903273452434255515658,24515114788957724724,80392013505105958,
    0,1065475700935874767522631694,3747668916701314601202802,2259270067658491647802478602]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1632 : Block 11 210 1632 1664 :=
  checked_packed [
    1129650020511397274634143043433586,3738179947466420695899049998,703833459964867106473784434,86891533791632578660274238,
    1579319591826605752472,24796165856959664154,2449074647350649004,0,
    23290627557297859081330,2746863080677419133144403982,12215015089501118532,44708991075939371716622,
    1483730807963800,11282200630837811089418,4117164642378200178,10717943992839835662,
    114786394945936632591462,196786515190543084949514,0,8525074453714171264084480014,
    331146786293549959660130608422555844883678,170199224318936699941949454,25548705445124776108,234737573334630872911886,
    502150873427183861441246346,4114966972787089892970510,535344993274486981664820,384632020156008108102,
    12346353677584318600,0,12245865998367858780,33273223307071534]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1664 : Block 11 210 1664 1696 :=
  checked_packed [
    16636679948667299806852198,92420267864755814797338,52376637975715389508,954593992075440838085185546,
    24216900720730030857008266,331860034966110867466,9884070083135074767746222,43878376293478894419897925767178,
    0,25103839133448540194,28811700407428456564,3061721628766730688841912330,
    93793313446978305100634526361956922470,12224735604574785546,2531868764050100532027436,374154593499082095470682432344074,
    9319988713347742322896408306392249770,3381166125607600112275466,12217973350097494084,0,
    13274416283092057669093838117151482852574,3509064319557213760786482,85182457678881318124920876,1628648329984776081454,
    51469710025307322,4991378387349331142250510,108898133252275049757353110212190260,315248487672106043473368453130,
    12266493691740307640,12617509209789960202,0,27264244908788143333571513290762]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1696 : Block 11 210 1696 1728 :=
  checked_packed [
    57411777053535309411466,96680427992012338237450,109408194766336474857078046133854276,2837013386402021115873464334,
    3066645299871880,90235695800396210507786,1536095049228332,533373111326346317838,
    31551585315699365527736,0,12449782537788596276,6285515907942384211595278,
    53677860509165043896,2802620497092297017528390,110173287037428612506665450016350300,11129165175960113166,
    4581474483715720007390254591398443426752373232047255361020260908554474501294,1634539098038994343936659466,1402238239845271309118966084782,38325108280195115126798,
    0,26531295693597839386,12791587188965908652,2880452738741012352668274702,
    38293364832888435814,104066309367101997726044170,984488296441460304126068,118420694265434772206129908813838,
    26121399568017932440,2547571819544580106,12838873382896279628,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1728 : Block 11 210 1728 1760 :=
  checked_packed [
    286760904979290110574824,18391630429143685625024522,44510764874862182806750,4767392103718801145077960714,
    12572565151586205832,3749296863578258556325902,12636767966357102668,682298655421839296474124326,
    1677714480527096901490406601842,207275126580916711854090,0,8117409711783042602267945472010,
    12572569583992455320,4303264808329105379338,13804600995187938895432673637971130,11368582348460265486,
    31318863162760245941384330,778564331842624453550805006,788092134891588,77353959708465406132279578634,
    279781786434051953237166930545095794,0,112723594607916139672281878768918700,20773232267520646890655758,
    9717523776950164864682648536436717042,185219264170349453251711002,55141735859295887412,12970917240042950678,
    25315956401283023032,4265440321862747100953972786,31238654968378765090892,7756777448215218936683020947466]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1760 : Block 11 210 1760 1792 :=
  checked_packed [
    0,2716989834750348392517542613002,39219791340219937966,764800716643614128137572366,
    883579523675201291702307326403818610,117720869693833336590346,451252342044727927906420,12811573282675363902,
    168803750337270789258,18194668039398259051991050,56651036547246660721320012,0,
    527362247661222638706,1305782009943598043146,13110383418078666796,137413699060109326,
    5165332674077835471810170945759813497504785774441333572933862729550667986274,2591026905962743801464229898,31647270251840675908,25658014056367263766,
    882653220888178027675800,104887565385673318862858,0,19952092863041689580736582,
    301064635212063746048136,13483485465206067234,22497283315357779506278,3365205948739688291851309066,
    10577593960587501850604682,27244493936456110090,1727305806301116768300,46374110691895912783941646]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1792 : Block 11 210 1792 1824 :=
  checked_packed [
    253713673714201404542807979194,0,458303156670145109172412,19916748252448515929673742,
    1330208847541897115243999056114790,105309981053342952984586,212798835480093270060,52069046406924978445340381234,
    689009931655304061516719713087596016341049818402264000542780681499981046,2294638781896030606879363082,3250641698824244,1032264368972102243094368306,
    0,301692081717500710922,105345304486025254412356,693458805895204878,
    15991546893282179671702647922,1033674448958672863236178,68608231312058761622630,239098230034948916514878,
    26114090929812947240,13642071673298603948342513714,27212299327072378956,0,
    47729561685762067152111031825582,19773452674062033763700786,154052626239987860,4448382389137299376263139342,
    53348437856370872,5581290319997046794,27490359680228663388,723582190729851581542]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1824 : Block 11 210 1824 1856 :=
  checked_packed [
    26962694057970992167272600,33502113535628448632842,0,1255954218359500668003185332238,
    431387252572387265019393126,5073416774351582083876493725710,176263767754022956,5042433954480511505980723210,
    47146935525803038880882,13303624534293745698,27513507926161498164,11932483503456784454,
    25844983972295069417608,0,13392160629624676444,11959404344509468686,
    55677738785345091796190901386,8869530746922546076061722,1564339863001971564692,5100102605932464805253222410,
    6826186621630779698222744332815840370,13725408852457820170,3329497298378828,25382249281214610281405528150026,
    0,159316838849796007530506,13753371243615100980,915117122331309663132671088267274,
    271423658563579055810996614258,417848774103050,13791078146499420204,252657343123163768164366]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1856 : Block 11 210 1856 1888 :=
  checked_packed [
    26962694058396228289315000,1214377582771346320039874574,286760907951270040445004,0,
    13737981219239379192,1020448400750378677400768526,28177063507056926764,4313164588303727966516416522,
    823808082566277040665796481523609002604280594040542956419259647108592754,13604725769401012258,13604725769401016564,35971653879782707270,
    28015522257976705176,14337779029740883978,0,12202317963985948686,
    40302677174599975585199458,59919343821302821514383418,13775568147580985412,74633361074906231476238,
    13666848870812893320,331860058777409556490,13919785650904637516,3949842279649505921231491086,
    278191180287320063603868972350,0,28170662478656577588,3143165902802406471131729934,
    15303531955760675541759078,1564339867537457025050,28222624232370085980,1427973714472865806]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1888 : Block 11 210 1888 1920 :=
  checked_packed [
    1640547129004427869245420646,22031077119251685469851658,735858146696191047028,439812817866538396670537077100554,
    0,10669989698060266966333001778,28398659838156844,334917340566961489186830,
    1100587102867673112169690226,4604977858201173607445434378,27368302331788533812,59696014726369644582,
    527362247867381068902,4697887181390062030858,225028376211136454780,0,
    26962694059034082472378600,21851005609623589677730631690,2087092504928303718468,14185093910748991526,
    14185093910749004024,227752891676408078667826,28398668428091468,14121513208837574702,
    48632709168452377523302,245044365919502576128010,0,10769951551167279587752153102,
    5278382264256618411881225178354562162,829779676837711882,56686724272627804,329586604901555593285646]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1920 : Block 11 210 1920 1952 :=
  checked_packed [
    1566677497663924123006256241718410,4285240734559139625177158,48885346374092050150514,48142496362641531867206,
    18786448695372035246,0,162846520238940204,50866388132110964946785800238,
    175635528542220175029506,1691766362463653983162378,14260979386873290820,5317475805242221866883485706,
    14163731915005247672,14390403539589402634,16206109907860876553106546,12619185771748790286,
    0,14038002362279268402,14414936439894581300,844838036137721729789202446,
    394457348162608497248226917009485056717938,29245777311359307802,29058753347270484044,1112440241897688209555460106,
    1812731593459352121573914026,1312350615002383078203068430,61159890076500500596,0,
    665478406959062335720,5204863862561996047126542,164678696007826885582900,103617452133581213427839635820554]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1952 : Block 11 210 1952 1984 :=
  checked_packed [
    455725768005197126345724802234,2940033416509156491268130,23013636991160442302911406269281382,5382961960185486238527000626,
    1763006761418888,563687209919347723079690,0,3047354618801776205238342,
    57411777736332030260398,14488268362420282806243338,29679684684877930548,4023054506126657211896696846,
    24731053143856710169786,200619457054347804807194,44635645187989692,13319908889911627790,
    42384734213670859981206714,0,29476817904720683076,4819080913386482047261872142,
    907571002735571484241852127640312362086,672741027482265718810,20690862197674701060317332,26735503666451361577308174,
    191343277746175843358555815143431746842,1012908478393324010131689542,61105020327400841332,8018132309680323647508494,
    0,56686861711577098,3016389124971162161389612,11954054647665941748127895566]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_1984 : Block 11 210 1984 2016 :=
  checked_packed [
    44160732712654615690,171014923337270355300362,11665839367884573174145140,4313164589496959766420787210,
    12333841984967516028441474162,36265364499740525334538,155178149487206017143939236,0,
    44166516091610329372164754988086590,28736532952125542434,14446812055480574068,284524562391985295398,
    50620082122340226315366,1094933684678633494954381326,14572666492702171260,4094545816878443714077664555432350981470548989579278,
    594523945799870993940632,31640948823731094908047370,0,4177619636084842099118094,
    14628975263078170856,19773452694462647383363594,26648763012312492684402,25164617541546998054785038,
    9328887070930487717877352973218918,43214260247142018478084460554,32022331093533860044852,728611085691820910021779132426,
    51023965354737230951538,0,32068106832943995953228,30224385317963567150]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2016 : Block 11 210 2016 2048 :=
  checked_packed [
    19219821221089076242822246,3305651745250380506730566,15005960086268944532,6427268985890866228686221679267850,
    34681034860377686344,927447694550602006470332430,14660688514539069484,6062920738187534636421190,
    0,30341382696175931426,32685596909389226036,1758279453840044182162378766,
    508473774338853228789896,14993176821560774682,62712975681235460188,5592517656003932227786248202,
    49312253386890384963299983544,281719605604406507081738,43349686662422282280902732,0,
    3457840130675912227176584,175471336475355821117490,30870465166289412140,13051463107939610015991599126,
    1443005970218462373565536946631782,344383263636395609034778,2908600481028158179865490633842,20466430430002333528100878,
    45498904334355674214,123237743961575434,0,68422399903192649306126]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2048 : Block 11 210 2048 2080 :=
  checked_packed [
    57411777963930937210042,22146220441325474007748618,483241570339756152201308,345181387195408311141848322058,
    59731102855610504,385705238494495392141322,30731011577071280172,5658003810947196599429763122,
    15303531983237471119881402,0,926630599991348,15323046410786443302,
    15724391363048915096,30716851974792286218,13196478402255599751586127940,4225501440019545325396789628075986975981270066008078,
    13196478402255599751586136552,18194668047935691963764746,156846569819691028586572,5102542146512242966794254,
    0,1778767446052457994575130136646,31181048343250870316,4898729534006867999592462,
    222989887819646171624562,15403644738418511906,15108962137050980404,14146011511338074944573454,
    2194942503129380510320571566,15724393579252027402,115949859473661138984530616396,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2080 : Block 11 210 2080 2112 :=
  checked_packed [
    60076186168262261837223969000,9328114236331837042748035082,64320931035070079044,63811375112956059586574,
    14703842161976413832361098,331860082588708245514,127615841423335468,2349014284617638022523908001806,
    20690862199375645548495000,6754978752665497631144444003124746433004777925244095314268170,0,7480428465085481231014957106,
    31456085781117943960,33320197364547325962,2449075403264893116,27248450254170755086,
    72218955748348090397810,2011215509147812368418,2011215509147812372724,4301145825788925773386616846,
    31602227524011049096,0,1893917364592716,1564339890214884347950,
    14479916356676907440690705510,29927956824080847810334730,33320199597930324084,15264431441883172902,
    1338751813777770254845229538489530,3802630895702026,26850106647568430675082,875292209962354312076722498965514]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2112 : Block 11 210 2112 2144 :=
  checked_packed [
    0,4593678058384594559505002401806,6155266671758792466500,1689738593330480688402446,
    118088684195819038979174,31650903212741890074,272461187128826699718772,1828906167087568785422,
    630066121259481999360184,2367950740150896849126952970,131714944251994164,0,
    14776117558197108872,9944375599775344274637328434,1051635758316738584668,1217671075112519790535643146,
    33624852464950080507445768961930414,61858657855344690,15303531995013240653362458,2928156392581974485677117450,
    18786456941709243506,563687244493353419542538,0,7638326690602847937234997258,
    179868075744571359312392254836,296114024841241782390794,4076626923979370668148,5933650631082134361935450122,
    25287995264111969294103726,6557518931630755850,26962694062223353387687988,309214457552723714773006]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2144 : Block 11 210 2144 2176 :=
  checked_packed [
    9178965418226386397956796251660466502767358860625943143134310,0,720189244471071790347402,82318682808398165053454,
    30895572878039728264,32232442645224362010,27359918593802026103922,64276436376793821220878,
    156846569820859259699448,3723043195275388683406311142319119596903304315240680257134025521189883914,34681048157596426292,17111076793904257122940489738,
    0,14680124908477677047818,26962694062435971448709188,27638365801156622,
    26962694062435971448717800,1412913425218641723396198414,39639073535545057348,32433804657819652118,
    9909951682346869663108969610,159010639101754850923807510598,16091258694586605612,0,
    3158542064173948459075952981214,123536075769439588454410,31821831619922108468,1462888156861569983292124921073674,
    31286448124621504696,15746339698735321098,68316614010473554044,45232176965098269095276917374849034]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2176 : Block 11 210 2176 2208 :=
  checked_packed [
    277363508767849621504152,7039256415603324184759739987747542899776842464736976845148170,0,1045441271762865031745606,
    31060315849975197086978,42636186497060538683402,57537316302483818217555894364,39308741451625401851456509710386,
    19219821221093886606194066,154052664894689314,32735772675309314100,29130888947543144187039758,
    10020061435283446214625866854,0,1972463726502012,3600578369426712285648722595850,
    18211060768487029013727760275055803558278246,18391630437681118536798218,131714978611732548,31576930613045760022,
    48696415176907921619431718219953254,222741931452264731381770,55735936399368951706738,16248372423882182670,
    0,1206661610571015721284800526,130090012699578663360786341956,1910731423777789391201636366,
    4331210760219954890781242482,1966899380127417357557567502,7597262525064507627151404,31815051847883821102]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2208 : Block 11 210 2208 2240 :=
  checked_packed [
    47030317381878377917464760,43355214908624176418866,177297538874256681607220,0,
    3986627294675080,58043104782965710786570,995899832541228,954393902757234738204734,
    13105616860639007762035958,562583691656780828381234,68080345941012389940,24584690253621336192585742,
    33204912746546610328,3116786459776913418,0,28909458418435100686,
    32629063479428093326510,32172643833104600374827764674465806,154052669189660740,46959210549804513185763398,
    33546379604451672200,162846550303707194,20690862201501826158698548,6142601357527352949591773194,
    1594225718390263283663779002,0,1004558486610068,9006553049955983680411275274,
    88304253797417144,46250804146868234,26962694063499061753815188,5102542148393095045058630]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2240 : Block 11 210 2240 2272 :=
  checked_packed [
    12129308710659417381819674646387111194,16159465857511169681778544650,33761409719106281540,1219960809627409353527005198,
    0,113325734405743145127946,47848235319535288058912836,4898729541796564285001742,
    286554577617297583653000,44457208578807170965966874,16648729530579558516,3537710408403667336803913738,
    189228202235805848,574376028555132487365845585990,33919603585566384220,0,
    16247452096988955736552670,1044548891274307498649063434,186970564332899648151596,8985724356675052547084302,
    70767314527742880396390,7564226001216303247468269582,39639082400357556300,16482403342992019518,
    640449447212340075315352,4679280718588111786646441994,0,45775509001205866041406,
    42220218837421277368,13015305076460305663719433572366,16771370591516106796,169705857259483770079998969384970]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2272 : Block 11 210 2272 2304 :=
  checked_packed [
    3149144554582927517237817390218,388604216095237214258,36214873898199556164,5560477961884847389259337742,
    18644206149687744149713363169986092217530,0,170180250448175148,79902969532051198316630,
    133947782689362660235445241396433651760867124767081345318920670190252563776825844204535492109481249902436555082901469123327090,6491838939334636566535475210,35396748162470958254268508,2955275181382227202070,
    29059291747914010866862,1834238473547544233880064070,34189629647270977628,35856436629346925159917817866,
    0,130288283487265357828106,34340902838848200772,19232663440046080841983743825589309450,
    527930849870703188945294865522,615931533247542644969482,34269114915606241356,4821130944823802948071985166,
    286149402143056017241190,22146220445594190463635466,72220281610822492212,0,
    396801651658529139740647634022,7038947921672278026,256254924562524,15587112321861011116046]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2304 : Block 11 210 2304 2336 :=
  checked_packed [
    12129308710659443121827046173471421698,2097271353826107985954,16794925208866660516,41285757575331525808885774,
    154052677779603592,71086616344738772553830410,0,2673412877263401579339296280586,
    564964490418474464370,6718747214931194479092292390926,4170623693627444,16763400316954611782,
    2690775163078192773789136010,1186842255716415496708427846,17243935591126010830383351380544793634282657003416701379596282272691338,15319857974649965031863619654,
    72218956086447915938990,0,17154902581114314804,14146011513353273599856654,
    170180267628052712,28537641728106888695818,33525340123305091148,4459773696198051075855487046,
    78337446249233927700035420344,16963107765071384610,59243471805318627865786,105829603392012488161007505418,
    0,26962694064774770119938082,16899670214688383068,23772703716059241254926]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2336 : Block 11 210 2336 2368 :=
  checked_packed [
    51983889885676188858,1249935891773248495297761350,27915492893512441924,7827809735948173610093383690,
    176264523668275336,17294368759150022730,160471550963753004,0,
    29824009667264404010122,324902863314912333008906,42220225486030643252,1276440474755230446741622798,
    24593000972645501080682627822793842,1394111523721005432563568690,73846809777634549852,295986480120284057614,
    16941787581042895813096550,4240717559894066,0,219617404613286588893622286946354,
    1287520506553087049864,2058781669209260691466,4249479293182028,561507410863480057624844393215168522,
    12232895764188156748005127390,3004139854001075462483218442,45939108212226913042702380,58866472779423753826240782154076170,
    33205710358963242829624506,0,35396748163709283225051188,8467292374569023144890208266]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2368 : Block 11 210 2368 2400 :=
  checked_packed [
    24072035491626637982708838,441193885036071122670456902,2274880610281954746516,27005658171891958058278461640714,
    17242625709063553160,78102050768383355976640697995278,72653362493852229708,682613179856630291894286,
    0,37406513459506450466,35706006085727952948,2063183393715534600240893966,
    8229244469982644233868530431078,35477120222161276938,34323474651835015356,73611339746114539566,
    5739675962507463671533891877876850,6772585110603351217051537418,176264592387743812,0,
    36502737039145870311608,927505531016555216371050268856334,774149604237857797306,35055546856818872382,
    2908600481097941983857177801902,412218503970135352545290,36026309096071241780,4164735942570464447041558,
    34913891135862620344,1533417519795146762,0,19841431682552364430708969486]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2400 : Block 11 210 2400 2432 :=
  checked_packed [
    25009744336882118329373426855899575518,36131644371596480562,640449453590881905942620,341143526285959659261990,
    37046359252913767855206,250428419545848186747836436490,34665532306919268588,6675356956914700412832976946,
    44341176638549029298913209741227194,0,17358388871475259859022962,208767305571904367190396112906,
    4345858359312536,30132470673389930078539826,36341771094961692764,31393036121847894030,
    79173232291796066776202,3054948060472807474,35443592685246488740,11134743197190464636719118,
    0,1844068115845044244490,36447650198172213292,124150733910390770890119843850,
    52200145969290743562384498,18391630441949834992685066,2318775674856523440196,5931176486134030060258070542,
    76286602027852644504,73959390452266307594,1401647940547469675339852,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2432 : Block 11 210 2432 2464 :=
  checked_packed [
    13641930243479334030447757767938,30132470673491566184632330,7662314874590271039878246,6753431307002338944506400778,
    36128708789689718772085874,6193313670186449032450062,74816929714459910188,35775656156012844454776846,
    154322957515272673571942,28891652473287744478515210,0,36763656024747937830,
    62148799670174863078514,13517741840441064577912803378,2171548881437840730399942128754,548607932568849879054,
    613015440837156222548325514,20131304399743130042541119901706,577628137875331809812532,120107652833410964230743527438,
    32629066725186418521190,0,189228219415666764,7660268855937116147758,
    615058825634953532847174758,73093640014044610240045912090,137135234996205047002214,5913094973570202734662,
    2097271367432564392072,396790275613227225098,39639100129982554204,253818840259123486539619766370]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2464 : Block 11 210 2464 2496 :=
  checked_packed [
    0,3594922388641416707171160078,831718381245096142053420,685522998883856131869904910,
    1108462335443080,342039076692097184567346,4450999158710316,40191113310028985012238,
    4048819059657669682699187626,24148843888261669589074,1426677348428158431404196,0,
    35844591469050478744,1552154877875110023194,37406646431693938812,540320881190195548917774,
    81893630391702591124666,8818081254271641146238177290,77473359410713600068,8780371955070802766222856202,
    75200008726473883784,9768920582349167756578826,0,6371105388831944946487366,
    2841702012690441506452943986,141265811077128725205002,739923754498279652466780,37406664161318932518,
    814190794278726211645971903662,46251164924121098,640449457843243126366260,35488255068378289448968005881866]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2496 : Block 11 210 2496 2528 :=
  checked_packed [
    26039066406370632567906527772103685306,0,76440840577325473860,27915492897807405078,
    473633472071087662239627702449254,208674445698585614880778,255725267877928244355220,8375756415395288430153830410,
    98259052821495019748446971760470808986662074,46541657066474940928050,76105743797212684436,112329944267175502771392526,
    0,1212962791687928856711178,607489983652688230883396,94256109268514182795278,
    25391445841897232063804530,142475299441111606497290,368898710207673225825263736267486322,29298260697646910222941294654,
    79051699911433142408,7542023679278806893116526606,1287520506557382008876,0,
    20543977897663775555732024,1495878933948358557611862559559694,42335737454475691958324,503955791095940174057542,
    36995775998956945560,1702931153090899410230972430,23503258692039455314818186,89436201950126188815655997804554]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2528 : Block 11 210 2528 2560 :=
  checked_packed [
    149192875752189755146392,6999234338642638976061450,0,6967726909812484032300060682,
    79539658361476759784,74992015278368132840258801674,827990638224639944831518389350,9259841053577484451104952330,
    51937825007983391120834808,7203567793262737392540848138,76118335187746562100,17732453327865749360719752597554,
    10885355809550317892212372594,0,36802060756067557500,33123144634105597966,
    472236285401630757287266104494,22146220449862906919522314,207879607091034522137714,37668653794825605142,
    37668653794825617640,77178875394406748186,37383821827384549420,389437282699113717198899495571466,
    0,353691701788582883627018,2274880621620668407876,1440231549156302435204993038,
    2154811854076483209143530610,77851394845584658442,29794841384004429490237218932,174958177552826952821130661950]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2560 : Block 11 210 2560 2592 :=
  checked_packed [
    96605858621361007637642,1552154878016843943970,99835632175554724,0,
    36945916674147631240,2321635977728026,65397496409880698827878,847533415677161981874214,
    847533415677161981886712,10097840418470091533848626,165155451170725940,62839881648407267891797299214,
    7228306034861818008,3608684597421805578,0,2000486756444540942,
    6157622356475130831770264382520172784701589697794,39845230107313385652050989066,23768114778353430744282226,6301875010383212731256803342,
    4227443317451858048370881674,2421915628147851661322,339193579908688623266238046260,7163321644962441235791876106,
    88592644498794670867357817022461030,0,55106458136532350394179660,94552662044733360574478,
    37287974329231884472,7883354816393138084515910,37737475753776259164,444558117416871800082446]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2592 : Block 11 210 2592 2624 :=
  checked_packed [
    846390430152524922412247037354,1023567727921584934962,154052707844366500,42102979563055140703309838,
    0,31867006468327227789322,64841208579007219251557730,9296258058535198352545419274,
    66261780261636719785074,80392417232031778,20370484004686450674488063078,48398808896855814053040142,
    495294343011101320487989425290,50540105031622370267146,189228232300568700,0,
    66317313563229461427302,48318321946267698,501041743624657841020435593360620663910,37630031984316125206,
    36128708789691161881097318,28631958865835617738865774602,82142103428376043564,8660471961536544495552978539778098,
    670113480726131425427608,1710717188889584828430684174,0,115158391851991407039352846,
    144537246755274381866086,92411121926934538,1796749867989606492,1339655675430754964213798]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2624 : Block 11 210 2624 2656 :=
  checked_packed [
    27374403145158211517131053059025155210,485845654085067345970,1514280276010569077628980,49195330599206691803238470,
    79951327164209578120,0,66215454814862745547962,2521034211694960404740071084060053514,
    124956088523117562672723082,6387549958856375294303932426,38357102463392161844,47128047339078405811343374,
    65663650068752966366322,1640996810418248591232680857670,81472454809306013788,107213999901904953724800750533480458,
    0,11717576726241258082475708426,99835735254769732,21763958238852867721141424142,
    66221626672902371975115890,330279474018294010220554,327107168611276721199064817780,230742771274940021739534,
    254318759054076503277755843947010209026,32501171180750149521458,7660268928504883585188,0,
    24148843942687495176328,7531935551479412573866037298,2908600481150279836850943177842,247497163287704894141632526]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2656 : Block 11 210 2656 2688 :=
  checked_packed [
    323423442649878982833254,77965633720288343494666,30953529652171974447261032620,1561593337951320488185805410318,
    1189598477089065627530835058,2122703669266093182986,0,45939108216189552949202966,
    2577033340928036814882447832166,459010858994898567172106,173138499959798442137498738,8923703094842403250214277130,
    94044711921858214147883110336836746,2068265220342735179786,51937825008212364417310772,1117314477166939340947400429578,
    1445809323845712151678159337567454,0,38710087539090268228,81335239622824824854,
    254026141105511430688304283800,61701112355499446976385074,104128416554426444,12320676814301774275940422,
    182421742124143104680277166,8818081255336759500541530122,39979380175949275284,14571025965930468587142756962314,
    0,81743399238903009290,44407988229149639007281220,12120437593367491121166]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2688 : Block 11 210 2688 2720 :=
  checked_packed [
    28042071514552000991743315702485890162,7634550475922123568030158858,83080410163140632644,395317770242259828084806,
    938613703548996698296,1760351149501408679269765134,33295619268287362244732,0,
    1079708863550422671232611442,2762477684910669685239844934,909691948072652653994076,7064474000480795843000012814,
    84251856017656135832,40237388469530267658,2443819207368828,921828806387472650997774,
    2154811854093338722397336750,1672559625368506418,0,9887120606630864935152783370,
    3091521763934695605602890890,906641618041619792007178,84574641570367676492,129181682308424966351097870,
    914023812896405793554760,83795056987067125794,39534302328812216468,9710740900518285956373024778,
    40195976370434621624,0,82684526153883983964,81540568671225647150]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2720 : Block 11 210 2720 2752 :=
  checked_packed [
    28375905699248895729049447024216257638,85152034869201914163860869146,40690114189374529604,10484718489015012717424149172064306,
    85557812578681372968,2058781764454455447562,10880033977679224876,63415545229764718321524019210,
    0,3796741405582299170,9690809084298666036,5906081848701208555295870986,
    1522101812597353991629431120082106,6791196898723954167818,1396062212845426272378996,56962403659275664186485292142602,
    359146075238080292743425310904,46251508521504818,39454339478098812996,0,
    69467966300867109336166,42336186388239618106,84688365516975251500,70117577771896245497163157518,
    443423557595486149849122511601546354,2594834552949609173046267918,84015796744271962164,116632475011548966817862,
    23503258722133088567047282,46251525701373962,0,346514366110499666589722991625506826]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2752 : Block 11 210 2752 2784 :=
  checked_packed [
    37046360853802697897134,7260739773884516926492770,86533729478768599108,156274125424447463624742,
    16997143517611672689427816636112011889695646561394,1739385336645892541125758990,189228245185470636,240492448622113701498894,
    1221525751566739757520906269287789706,0,104128442324230196,3004718364419548805551099918,
    70439152211790821078118,1368412591231479905783818,39753223433118294140,233236632175722310406166,
    9582810386996985693654686440233229104314,1809985110113232530108846094,631188389634116,871973361222734197098488850242605066,
    0,61511762976546247151626,85099083894985072716,338215908801588520069472458257731598,
    149192875754526217355400,77788939311275864119622766602,847533415678914328535084,158224541182365815355215886,
    412792464646284001432,1718940324362981386,110967631660957091122705866804,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2784 : Block 11 210 2784 2816 :=
  checked_packed [
    69704135940839783479589745850,41484125391460241458,2003969191822405161917096060,9967325516984006853980590130,
    86814388183791321224,302671731676600174907442,104128450914164780,72917355078604883318578090054,
    70991101867563405030514,4812585979626619557812113418,0,55908554979858046347382798,
    42966842791874684534968,329482222199241241710825530,53653917208640620698261928905028722,2602377189231955982,
    203817537687154826687590,2769344442030701326180028426,40817749882409328708,9347857161976357852119306254,
    71447483372172845528250,0,85192646649851158700,47694547302803239518343182,
    149192875754818275131736,307943587724533088391218,43313521665306009748,64451732389550415566344206,
    102467988641302702096402887818,40434581168124334090,5081882609852508,4558617661173047024947214]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2816 : Block 11 210 2816 2848 :=
  checked_packed [
    0,24385909795024725407065706506,2781984029151995885527108,162249582777930779235436204046,
    16064746697107980424,40753563534811467802,47586781315586859052,416207748013994444591118,
    3983340640751317603955258686,819234275988112150562,352186480749191220,0,
    571407486457256370465557984478,699979168048341655228426,41208132867488489564,4093622162794808581264773130,
    1406393158185667970120089056497907126,8532851825026535474,8495708760619667857350868,1066373283591834081272455894142986,
    85328479892218593416,1311079810488314401656842,0,4318920071113790705373230,
    156581968584489629136058,4989287070001269732960613961738,89298827362349097012,113646355066392614,
    4291024025451690763548899685514,7242708735813718286115278898,196980688607575015432268,535403589182964109326]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2848 : Block 11 210 2848 2880 :=
  checked_packed [
    3470812638364166575548654433646,0,846550280877112668725436,42616183683331133462,
    3044415482915092963520427110,137673734498396546273306,42361953238957170764,11501772222897987046130847754,
    4874073743794051447236080922,430925126202073416388841482,914469851969597298498876530,44931880297002655192977422,
    0,42617522593214763018,6088536723098855731634252,102837651382539915278,
    23503258737834114611688586,258630761704853102540099594,1651942019354357235982452,3117677698205819036036501518,
    41757545083992817800,35196371208547566882826,87803274827745206316,0,
    37046361407956558296166,1937279475944009209447714830,2937496066800445283480122470,104847210966326303526982,
    42834512806120800440,26678017556221962,72026984616056687977553736818,59888825729903033739187557765130]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2880 : Block 11 210 2880 2912 :=
  checked_packed [
    7936077317799731763882780911810032030224736434537687169278003480900830,8135013608058644492527341578,0,7525180263095847675832045582,
    294318196906978733912754241688,578765913855107280364032309071886,97653144340505042988,739176979107834885050406,
    203817537706121402266738,38548857230362287557012623370,43313574648022573108,32913145783250483180732948680714,
    43003781596330344600,0,90925355529161154652,215274604854578778126,
    1459681583868586633984047330406,96974114346579696653231460362,4173314742094048140391828436070,42822876991317872662,
    43338459743564873864,19414420426399340105968839036998,377057041250374700451601061007125515351214,42685213435769769132171028598794,
    0,1191120886601651064882,87435274738043199604,2520539303528770227358666766,
    1945407550147611005244421234,8778167792047230986,607489983655316750868596,2958654750749600843305022]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2912 : Block 11 210 2912 2944 :=
  checked_packed [
    74022806849049283540226,95744225079546534514659338,41795541635105513724228673612,0,
    611933318604517715050485527690,1844068306335433756682,88600235219590586444,7260739780116273954820110,
    3717127310197128876717173611967746,5274640742092834,35396748171882228032217212,112182494746352398897166,
    24703640138483353773827526463403180463666390269931552319286129226429542,8853364682640068618,0,3794596259107216297998,
    62357269850008889801588872,7224034417692381234,826308319274132132536680232006770,7670000341027173135846215694,
    73129235226004140605624,90584201814368849946,5610084108060968703536166698702950661476265058240683441926860017013634222,16681224660668075802103878,
    565456075222709229397750970,0,89869171964185157748,126393264562445760860174,
    3329215260537817220195038310,43465201351647039498,176265417021464668,1571847322998323286030]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2944 : Block 11 210 2944 2976 :=
  checked_packed [
    2237158079802283282048332346614,43864259515144736818,6323654567928067417710644,10731719787521792218952269565962,
    0,373541408184733722,64841208808242199503320286,9875838438288368877302714382,
    498848125154448103194808,36389336080804763949600778,88569389853513359476,78323392193356799255947137586827274,
    434057834418554034997703782,168908710036288514444759090,127589732475258478436299962,0,
    2908600481211340665343669449842,7736622130126369698353166,195612057477849156,52970337102825285813800974,
    29638310974510296219800,34290153986054439871451146,90200823375488622668,16548793106441820520779370991686,
    760973551097974016196760,464883637762108476767604746,0,18632135390856338965464843680747530,
    43268428679379697816,218608519873491762911372236591992902,89171860240566591580,107384598005836081893296050214]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_2976 : Block 11 210 2976 3008 :=
  checked_packed [
    107384598005836081893296062712,78897483952947080482957791848304710,81737457235687033020468,12000816057486387719274762250,
    12969656238584381576,0,8910487569337139096121557379054475839198460687832638199761628399940722,265517052418518505492494,
    64841208830716217175061606,41795541636457764592323399706,220006857001934900,9960162207384211350087536654,
    19306495608591761560,2015395583561712475853295630,89963428553032736860,599318441206329694293911228387338,
    0,9081421032446875192453500938,47586794612805607492,14755083150900304961430672642058,
    95120586857854825149554,16877706108244872592718528941073109006,51937825008768442423058548,1401218067975076878014713172018,
    41795541636728214765942358200,9221217648570764442740985866,66544768554115333766520908,0,
    75629209730982749418634,46251886478626826,2561297426379478814668034508301808742,74376899660380976975934]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_3008 : Block 11 210 3008 3040 :=
  checked_packed [
    76633186482708971271426,618454243646278052352034,508623232641276433145948,442286149059341923127366,
    90922986478082474120,1392297054085784134488074,0,34319690452621560590841159880754,
    14347064783903179705600226374878,153058009442059926760329226,40983294791024342048383705180,10796291200950182061635801138,
    75623462239631040361542794,485845654093657280522,81893631158062195684526,129473385696911507329038,
    19070073164575032440277447998,0,19596205488234045508,16785985374399733998597181450,
    27486895402474347796957556696429670,11968721814425551507482,45038457283787366444,57169786755219509612093761006866442,
    3442236984714545102204187966,112142749404532773827964071604236849166,91822488737110040628,7525180265860700230880595982,
    0,3110345242601057308077199430,1551180190735772369821764,638734652144401518606]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_3040 : Block 11 210 3040 3072 :=
  checked_packed [
    45053973874957687380491771694108652658,7738781804942988553079492618,903371295360521345179700,93978774228019712022,
    93978774228019724520,8368430573811520877616959502,93241686277012594732,0,
    1555880735520328312176872,373541545623687202,5205643192636525363045872742,581434159186775822766731956234,
    45067614934100614571355539832353862914,13951329893222969644159026,44756692567509180508,39741448719073021966,
    51937825008866573835845784,45306191958696267826,0,2628327263380004933702,
    43976432989295886632,45746046611010621466,1764574354817456638271580,10954189426467548767855841290,
    152496788488387076390347879562,67509733621664936104018,11246348100089497526324,13823932801920562775461902,
    50623824998922231961220534218614256972914,0,10313022431973590758057849958,99836285010579502]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_3072 : Block 11 210 3072 3104 :=
  checked_packed [
    4763316090844536453338248294,2084044793792636858042159114,92491582368022274116,3343596365778359497007304718,
    78361754186221013185818,410151277162444064034826,95050744463909462092,39712210656836651508421365774,
    0,8818081257466996209148235786,699358110556212,2672991273466515436397924366,
    1777089058757801016311944,8759931852108559225458738,23503258767927747863917682,65740981982964608191696934,
    807708875297079504683192,8488408072669918298030215238,724381387522995464211275820,0,
    92425107921963073768,2058781859699650203658,389533193350570611310399717383166266192998,539483823136621316804622,
    23503258769236166700971194,175806281920861416984586,45403435614888534068,45475834721908822054,
    11971630964441060541883079472266,20917633152551227402,0,12499859892074788392418676746]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_3104 : Block 11 210 3104 3136 :=
  checked_packed [
    5480449994938927669563755316278998130,2093511691179415742258876430,79020901916089427965030,1392434505836692071252436315017226,
    2274880655636809400568,228800751000883226,182651641096364531654708,668650449502492713501475582513162,
    78891908390130550846566,0,97653339366380019764,6265147533360467787848355890,
    1543950184987512757777958937659716710,8595971930539136951259206,60410094994949629026380,2432471758704480270,
    200649139115901344301624,7944521594958346797189173258,215945513734343382545522,40161097547622850809910254777667594,
    0,906641698619054555664394,5642633540018252,231183152706859481419946819325966,
    1510761326924956643052500082,10462925733075722980370157582,39127675174513549364,5640820252858158243080931643402,
    93625272417558479032,18518513256394395658,46641356313016148060,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_11_3136 : Block 11 210 3136 3156 :=
  checked_packed [
    1056975352080259398779016,107641858426036944279441418,46637380836794572868,93500402662574607589407985678,
    575900710960527014477250442354,293395231041572132884490,9690809118658404396,466889722245627676463118,
    1035570367833027255484568,58845186275649258189230090,0,8392767017834694751354320978972722,
    94079032613025104024,39869328303557228167380769280675024910,135631151622934260296463474,35866889588929745741960192200714,
    3583511606649201419343236183178,32445384895187419486731487940622,238593872820084481728564,5695203939717142]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_0 : Block 13 2310 0 32 :=
  checked_packed [
    0,15801726682533898,98813503086636,428784053990266507278,
    20744315806430322,11542878819979278,32660564006150188,38457781677723658,
    12265162648073390,1313673777116090382,105942273182670892,267011435533204197386,
    241680421216076024,0,81635189490463846,325095744693577191474,
    87133170006493246578,2826572882431424098996234,1569048722677804,19246511342751794,
    44332898446762587238,40109816124424708658565130,952434081700782132,89854986099363850,
    780903861874032654894003572,524466733986091030,0,77588838601841958719502,
    266553074467620271218,29667057542796839248465930,6533292182478964,647304764807188490]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_32 : Block 13 2310 32 64 :=
  checked_packed [
    1131677873192336110766,126870345969722342210801674,1416680036764753964,2953310535643807354890,
    732195449468895560,20311889670913921038,21355215731040420,0,
    1549720735246062728594,1125785151510149074958,861862710084640812,21420294648495083530,
    7099629254492296,2746103300624398,8133200545299730276396,1978723734772518922,
    313161417570493470255101282,5588137036297082507278,495297771872300,411442267324342427717642,
    0,51438643054301417494,174374596887774765100,4628647607168667658,
    12714349190105264046376,616789946518995325685770,87981320493966926906980244141170,1228264378202102874247182,
    5264340521484042392,32161724103609290766,5214513681391427652,190383924688852094986]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_64 : Block 13 2310 64 96 :=
  checked_packed [
    3071124222880314831986,0,5489865873118208044,10484552276352631312394,
    50934329039995360761505395814,5802770681632395310,146892075516414664748,3046239608674193418,
    78982923396424168892,6071657676268376086,36198096156696839725124,20217150584910107381770,
    127250746591184566016291954,2765335007110107150,0,482151609967852363190286,
    3475082378207249314918,242862566315260384198529038,6777559065506619436,983511206250005768704014,
    6670933135129067704,4504239362805187680931862,11580869059701424411136499756,1412576503408889866,
    3079009674396436542686,373467980519180820096749578,3661030543073484876,0,
    14527802652457581195200312458,331978226398410859064856586,115757954375732,84337963437695963146]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_96 : Block 13 2310 96 128 :=
  checked_packed [
    861365192791492904275271032831516498873557278739304978111636123801593328958,339052082658604196437168138,8145871930977689644,4027105449118535714,
    1224537406351360344,142191428482991747239958,17648077365709905988,382768928299315013930192910,
    0,44708991073748938395662,205250271482514251820,32721031337563974382129162,
    26413625861884057134889857028469874,7808208501762691086,19030550372478361652,9235897334146011146,
    15616822576196930778478,2499053753121925451780984842,898374878695006252,9195815220173482670166026,
    32850779303393011709030,0,20181657234619100045356,267436090744795028151135637574,
    7293506786035091681602188510,1859056663777379538896586316713994,9775258185655918684,11550961694381445154,
    20542023593860546696,20690862188744742497423382,10315301462774653140,78373070968454672329740298]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_128 : Block 13 2310 128 160 :=
  checked_packed [
    5533587458993344754826,2317427749175693573885966,0,1384672221015068737441632266,
    10576606157445546360,4153741290281537376270,8931228367953338420,3560797197073150837264398,
    3904147597075818434715989358,4047319908252389398,22859399655415881820,2652637025752520264257546,
    20526800870778689565978,10117978925171740686,23930057769133023284,0,
    16918595567613960758771864,1137440325618641145878,24099810469818146860,224141928657065405845514,
    4065414238964797161608,142995675150376903905294,105345304484272907755564,56020225878921226,
    2071042533007626871173726352522,3496421686276266019681996810,58852325063711791259692,1115109661547698618361712654,
    0,286760904979290110562326,10736469309992522649444396,26335463747748892698]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_160 : Block 13 2310 160 192 :=
  checked_packed [
    43834881695961645332837634,5046052871498644064309262,170180061469614156,12918664840396457417398816782,
    13373996874969661592,663681442676541736306724153856010,13493915407676874804,819541401462634989251203086,
    23369023121153377548924636,0,665478406392126644268,2679001762852462040977418,
    13805900618595844232,15021161472685900065808987459594,59139741561602973748,14226112842364358666,
    5355990459643814091983784434777207910,20203172472019734061125646,3531017163907116,2449075197106458674,
    28710460752601014306092170,2769421948503256780312154122,0,3395619705211404321105645582,
    4017365475479282699405898866,1165055658505104000045551626,3688728363016284,243372687307701227554,
    15158638587060965454248964797722,60076186168262261837223956502,3767583962570868,66039474576936669210]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_192 : Block 13 2310 192 224 :=
  checked_packed [
    9834994290692563056489664873484006802,5189779437635664718260604942,27070777219749603450924,0,
    969923870343320,35775656124854059313139726,15864354800318554180,6712260986788873506826,
    2908600481059560891661749859574,324865202016636685520966,1101041449126136251424812,6341602427943965041562226698,
    265385860623578972296,769880051649698190069774,89544384305645723165421983511690,286541817711238886461450,
    0,37892701776056514299039758,7228306009092005932,71338354499551573646021496846,
    1047851756962040,25222173463103359946766,67954985606953225065789923372,2129556450316298,
    34209455433473622608,4302049692880918,186970564334651994808436,607746825990986919523127310,
    615100813132737557618,0,74719259630292181140,307197632757936970272778]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_224 : Block 13 2310 224 256 :=
  checked_packed [
    62654074081454208332938,45939108213712903007637566,36502737057287812161628,1935787998629366599730,
    464301352931969334522280948838,9900488516797537267486830,56308548393672651878,1969989177112719790090,
    5467962672920975827285106,8949306876213589970966,0,13143750310114745353506826,
    1626483248101928824243126023342,10503684553721185699843018762,79513332366952112180,288609791235871509319690,
    895564957369316453400760,655743428906342822879425381837836298,43313424530325643308,81372732153825071154,
    39024960700648800440,2317689251471567097870,1381960578491758445338668,0,
    69348960030905532953846,957476971457141542934,8880498372672155012833324,63258612764462771385405450,
    40943811961435472296,90128055325619684528959262742,345279730457144915866062692396,310811781984515331723274]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_256 : Block 13 2310 256 288 :=
  checked_packed [
    2229757444574347745416555017438,462434708190388895617094,35396748170643903061434532,2540578360713459624566591502,
    0,250242125969287381258254,324997677890285984509075500,87842993315204042826,
    23503258743067789959902634,165955373978993204423299086,5316617115265577156354124,505803214019661781798922,
    90417439505601544328,51921136615801768382478,40336190140183058540478341164,2421915723393046417418,
    3901005504161651407274738862441346643226,0,16064746714287841324,11494790158893666986172092430,
    90734232479423545528,1353719227800357465773844044365959178,180434389841223748,45689645436292304906,
    77543871747820716307570,39193033962385219648491534,2388382373701725695516844,551409740968936623709360138,
    212566492418425128,95291781833633566766,0,3233122027668252939666853958]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_288 : Block 13 2310 288 320 :=
  checked_packed [
    10950815856341707759349160606737158,11368672268450636371683446794,8949307179953677148204,68157919220790121327497274,
    11147172992686584375545967730,11768959265791006387296276490,79575501450063755878516,6245024334774137316968501318,
    19774277841282080052425471449751795807478,70481585355255076059061023674438,100304635613031702652,0,
    6551528143455552924565688,18632135390856503165132756958056458,45939108224857827744686172,906641738907771937493002,
    144328593116626755227123466376,11184772298199918346023997454,99836662967705644,10113168104816575770940936206,
    2214717861245520887955784,6133290603909182,873458179501709162717228,20932840716918329354,
    0,4023272516721503520165910,3128679762149720989740,753477956679447594668082,
    100124034713746686248,857968237279818611848279756810,41795541646193970842605461548,405293538564559861714954]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_320 : Block 13 2310 320 352 :=
  checked_packed [
    2319611083442127462495748,3494215775923833541758998,521517745546585079554140,17231530088598642667154313226,
    679395890577817752,0,236376536735610483119235116,15782709128732007381992476686,
    593862952370950131846187570329302238,212905673047248120482794513109002,3106911375353529677914156,3270577425480943734583378600529934,
    7374016640883355403521733178470,2832360761345445902,1875517780870132391747628,1382717145731414349582346,
    40211038476449612325467742,419583116254584695240527942,0,3466418210168358115162774894022726,
    111719965846640017560,15741283529443754136777527310,293476606385831853560963116,114683963328274894858,
    95254495403571910030438,16787708099956136837386254,416939366502366489637560364,57602586542893662618047746058,
    55705741504135839976,5797525007353516046,909900670448552648820,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_352 : Block 13 2310 352 384 :=
  checked_packed [
    3617408121433379380417064876872566094396666994,1946282214712523152691222,2852897624717457891372,1155578344868835332460554,
    17927383720330284939362440,128552872751251587076110,688272566732396070712506,1656128767669926113579018,
    1254462772504833726366232,13006008239311623640177446922,58338296562475606108,999511986186083756937266,
    0,104343777734710792206,2391020376357345104502828,40735897302872737555697305280057358,
    47306947074142580200653746629155723126800690760415314190699701131555954,494904966074003795211462905866,121629110648117927980,23208324255155633813566001162,
    7377456730226872,225932152402156073829535758,1948694159664615530564,14709245975771449172955186,
    105191257971602271253690,0,2083961266013102388813868,59855913657646994734190602,
    7535167929336040,124163576025639223403299125862600714,203226653804206170891880505388,725281641159622574215218]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_384 : Block 13 2310 384 416 :=
  checked_packed [
    5866779943421029472285529505047524454,8372700313880616767510,2989562535084900229164,455987607189326724599858,
    258988704440921374904,238541910500862830055438,0,128082505757467086858,
    9891834895829840998,349366553958016617158103011342,65320399963045240956,221328167444608987963592762,
    62969285208950456456,176605552563226470582413430798,461429694098615487193686060,453818536064857986767523850,
    126646804492280396897072374,1175308260902051124377435500449802,132549728108399304748,0,
    114557058960460081018030,133153322123321675838,1046654518374562398651451187292,6109896098401226762,
    1557306111030819494576264,66336798287643807766,8589757642858670596172,2227890558988550609904290762762,
    40809483973301895658276402362,219664062140868534181948297238,65707769832876810292,4117563554709723156490]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_13_416 : Block 13 2310 416 446 :=
  checked_packed [
    0,137638878840234261805535246,3219678026247008428076,138630389491581325362,
    137979534366545559704,27873813639485437147918416377548810,66415255985264754654055505964,67717272313821925386,
    84904545064686920297376413164,82365133889594281393393678,287216347900658327868,4808757436030596878400753734,
    3467970844023186478482813518430090426,0,287007315984589529204,11709349856778073600430090,
    719312101632863331598483704,105185306726362618865389582,8604099389956140,29209371085230837810,
    19373808422570761366333938480242,180231540718563082899502,2164972750643268,320943744029298762,
    12803036980531386183192452085593226,6032379574820270063216852855278276618,0,6967890167619635447021508235278,
    296577984379404435752,80734106033336841966784090126]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_0 : Block 17 30030 0 32 :=
  checked_packed [
    0,11175343388287551148042,265806943661072428,16506565719980109427904538,
    2159235775076515992,8071190391625430863886,12563480268851885063020588,78423284907672829169690,
    8058551715196039083506,22779504664429929198260238,10638952032502816860,4203932524704369645457422,
    26874845236979319016,13737981219239366694,20690862198099937182359596,627231386248126759178266,
    2908600481077006842659671651694,0,577628137884402780741676,2170202307040991659388047374,
    41911023159040032952,44426690405930635302,45204085313166647348,49430363854533213897290158090,
    50014336153322291792,58562971504781073523304042518,111463264561536180268,3442073901634383187009343502,
    7219745531117704,124315966152005128214,391861935736688892952191020,38711104544853412030713866]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_32 : Block 17 30030 32 64 :=
  checked_packed [
    271760329056077231242,1955526904141130804236302,0,9508929402253036490778,
    120820190161966255325608,17674099280427216729207214090,4316541799125881987124,212502244293091093874109965144074,
    4672744087939473976865978,145498142989467262438768381974,1510882936213347999162420,109266994218422767642,
    3485714621907149102767356785766,663205322053246377271496718,6712379990281127756570668,7189844777286846715237765134,
    11901758506603273140903282731999219638507220288699907833563836373924188698424991041646458725115574133713110019874095577364985204,25450332738726249040575467530,833878733136270992760381484,0,
    214812069978112540824,609190292660393449508311054,475996649366233332,55315679459884511036794998854,
    14667659649812403336474,6160329019603009146894,495336485289711378476,243706926318420496442,
    247146240166066143560,520942255124986728470,7583555843824736027030630,369650900106481714]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_64 : Block 17 30030 64 96 :=
  checked_packed [
    4079229097536526034679006,984857648763968799488610326,27296876009758677184185932718132,1465162187472339092901898,
    0,160686874161441723672120266774,74881152185182086766644,796614425579928460831232026,
    2565651792293994860410348,65506139331932190337773953093646,154963687056572330025004,1358260076358021256866435082,
    32540256792935164236808376,607651811032062893120239514457145872394,1120424792813591622668263468,673577831598789759058,
    293715576304276919580020,26703523681702468906646826389526,2582477807303557127536052805676,2342608263531917900290407272474,
    706694331125534310552,0,218533988436849729588,689880881479477023532388402,
    1755507848408353454559060364987761416525476467330876975363546,2795044706034999899967725768718,70282095085605625900,2440747763003886654939641942066,
    780859912372738867336,41582478283920291935334,4423999692520477719273524,1091308584297993296312012810]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_96 : Block 17 30030 96 128 :=
  checked_packed [
    318133973995386499028050015796,6666750240781805022928179222,38937011090473393070124,48221795999008353064849418,
    2717588641122632056,1186335830778563241238440448014,0,10066410948433026846711546384394,
    3417674700665186772193141587994800440751350,3054473034685301589860230893582,44172959552693182390996456972340,7198174498304322606993418,
    118498046128607121654104,43697422644470788132886,207465102348192271332796,63197659240677998153699378,
    119494577427644501550370072356475180726660117618,3919805283643795968046,16495978874059369002188152876,4232965858249127497738,
    4023676277411922591896,6001244345408574993510,14127732514671486465313087532,0,
    987621427576538432144,56357662023787354381770289057814,2079714995171990970412,308227025547385068695718989838,
    4270716200374159556744,1027666044862228074518,27791526378055442532251486277083180,111016378530539946119218]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_128 : Block 17 30030 128 160 :=
  checked_packed [
    997601558906839305537745884588111287106106569902,282163514974779177290830975046,15240928039443793737739673644,64839334634568869220362,
    6267643104652705976,20432285331516733983855183096975370,6200538332737684845371444,2258243910466561494824943357962,
    0,9134074316838361185782861838,577728407234265990832172,357074667567264089247770,
    47356616286830311993720618872481151961880622644,306570834953361158049814,6458276150558266682434262147116,89145861265351949964500759744538,
    303646303054914832597680,28390470410277295243661326,61282151887554561974316,129146154661269718700042,
    9850219505732931515637664144998440204832355730,14926934200078178694526871905055905308217394,1994268060839113602309132656684,18791483711454185020045922330,
    2526163000210598429328,0,3367154765888035429891973172,88986311209361575849163231242,
    2580862546168166498440,10798593848719799186624534,289173485364825772305429642,8307058728412217160069027991562]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_160 : Block 17 30030 160 192 :=
  checked_packed [
    157759135548101075483712410539123753891182,35239017288447299598,223629449623693440113148237455404,60983083929876265026195482,
    367677377950542520527221009039307811164348511604,26695059549015637558648901654,9157167486287027349339334778924,109685083395428247048385242075146,
    9713425210344310591813771000313564,21600285091589016272918770880526,0,2800689508516339126298,
    959601452945131256177246360,390712124404023655241797865486,1195580704923730334196068,4789245747027478477567097283308163098,
    50625257319913631372031114,274064189511875391228238624949538826,96964508897327282670018604,6694895937178832906,
    3070369287557395529976,12199477535056200207069591113742,213915826803893224263888412716,13441681824878044465115776946202,
    54655066358562853585172074,391104615673829455223877527408690,9405132655525470848224094855220,0,
    422680073376560951869592,2418632972535192087061627670542,4686869328727063651190457770028,49446841892492636029160787994]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_192 : Block 17 30030 192 224 :=
  checked_packed [
    161744836216498281736603875440132,169446866271497883662,103206204515697754492536627244,35237442227160242801359196186,
    1331396614926978068565213320,507831506886131589092795748422,3327973593632875749524,460369617094873106181879301553063464974,
    1220516782767088436892284882857461874177126,560411194426357636174477779531730954,26223943655211139791939706924,162866771553459577894005905519042613209868328825473639273415591592368490735416770728163629789614090,
    0,20613014832433391172475055771758,3388954851545526050884,276104331217236727444594,
    56727727950786955864716402,340913798921080817465575339850851873198090,14659953027942077964412,13289695076480295131169165338,
    1465344158660134197803464755196736650,19593554783516581024344088893558603387010,178309263750360690036522126155820,443610233898341880928110358736932934,
    933120099882211028796080,7402620102972798585796562958,191053799613910128533548,7461159662629215539258,
    3300716963288080147865561311753402,0,7992472779721592569721492873260,3525498010025546460210059530779758602]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_224 : Block 17 30030 224 256 :=
  checked_packed [
    11758344871447000686564964854429044,296767715195487883713484077142086,15618448959636380852316,169258181325287066886475802,
    7768506820511844548856,3548778491214176410234720882702,778131781716712724916825642513546,29497636565362461672421887840266,
    47937578554990462086401882001176320014316988,5747231964002152956813446746134,253970414443266557616316,1418151400347460932814708889918615240839238,
    53634432980681032711812270,83244877290733214711183271006278,0,116173715263316295684146,
    67668606219164902949429986,148148156444035780718,497807320744191191551228904480812,2313498514760405464829479983517710,
    489497222943356756512748658,25184917355227603631771127648278,109015556351949262457185247276,35364069036851562508992909338,
    60785935789214919410349572,21969994168393755630267438993430,4106657684159641690156,164662412906022664916482148806955078,
    300474333227668704206554507788472,18338230244264657293334,419401753972501224768943278,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_256 : Block 17 30030 256 288 :=
  checked_packed [
    141166469862050546478982572815474,1352173471484976049775024698737850748768266,2908900949347446887404363740515215961311341805838388,51852908218906148781066031130,
    8858862375446465495224,341605194049122632705511494,38672070715774483564160496967724,91049227481054765148829711368757051636960402083850,
    18748700049984586810096,24042114431059793009046668185614,623444539007287607959756844,2978223788695975989133984141322,
    18443632606404358979816,11092052151614933365081846951782224714797066,1115399707723319495763144220724,293168709421845494903083058,
    0,80298949679066791685573337681942,111088639704913539069324046639156,1024183266670837255790137354,
    18935804822442127409304,2480924898418499267012984602181505034,1422762628911427164839988,83463422857023234397704290,
    6398547682799319997494386,26302016893528125888349568241678,2432884651723099178278956,37641524654499647207130659819530,
    70744468649084388770857192,9251710749643779067163145408526,920027784718792013602644033544244,44183655797051947601780281370]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_288 : Block 17 30030 288 320 :=
  checked_packed [
    74807840873435754761396745696628,0,312377830377936119913003360332,859831409942136513762171031602,
    394498447256546117529143556977850,8813728246459771180522372337678,38574904384940628617655515881516,1749841571290224131879477210561646606,
    707873352912241845214546682731652189417831780076428171693621371745778,42271386581691032008399293255702,20357804490772715675724,5156590153031934873952176599910644006785038,
    118474298958675572120633496,33791200449788752835167173249127455658034,1146979075330466335252054810676,493548177893609961758779752975546978318,
    7387706029149206252622241721234690,512281494422091462669766670,0,105953241874295051784202,
    618823052369061494636164378,30621604981651670044710,168884457807053604765686978060332,54018851934254930421987938330,
    10596647392556907266640,3324569221700851069037460852750,11479942235914640564268,424056237637328660591796543295498,
    43657301100933440094344,216371880456204187382575245962360480895252566026,555482384226063634340519988,2955797807363002418]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_320 : Block 17 30030 320 352 :=
  checked_packed [
    113222195187642050825550919906406,2008813813183640261652407176400966,401319356685205287970896953221172,0,
    10639715533113964642488,1502657122328418196354240534,150883016218551922698628177600556,2650432301054523459311644836892682,
    3937670004980583566707159084713722775286605619934574,4276978686325679310313563785007126,2537876977660001926520876,1927469258676661588418629658,
    938605300617962313058271233115835070836827605031726531441573356385454,2049831024881245830857331475088412682,11266464763637017878596,874166674282908789613006898,
    15696207598354662157090423815168661498689661331519841088206813242911046958981331621160976454917112859791311818440855619925508,1945907746592815962100982616134,4172310845892504807277027984941100,67154578129417640886669322,
    0,7976407827407963266399184141422606,11191839166595418038324,218094174266342980374621711241286,
    435285349734454074112243132,376541157479484765935060914222,945324632650549544624396,2198313293735029540059615242,
    24289971213783808360584,1379118934422694248086623460790286,183113415451562296007004182814764,35150495783310003223590493753370]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_352 : Block 17 30030 352 384 :=
  checked_packed [
    706993561302323058679231602,18718777133180340342593295486998,14212168897201086151230758956,1971809665646486031914013611526197262,
    24188346566475031527672,0,445024584913051422941595574324,10459772650246690574503623266330,
    92796573154731147611863021180,35690632584571121888518220025870,919069692095333629610361364524,351860609321245651799423510430032597042,
    669280305985615786856690874,72964479012696265715701780550,219442631495307457704322125537332,4946195327039346992472457414805819402,
    9173769319765585505965075335230782,187786709124468403416902240571406,1408823169911994399617720396,12007766482751498,
    2572621772318921388474744,1147798333522505331829116950,0,31130934216892197209287192383944308822042,
    1661577953899301351816098248172,466880320364209538883596750688278,12496007759681955045420,249921918070440979363046363146,
    68634371597836328904260698537399812720763880376759108971279678,27011764533231357974,227512904883399311515661958651948,199089437261390635587570289864609806]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_384 : Block 17 30030 384 416 :=
  checked_packed [
    17211492581627155267616692713251137418756,393604418574073252527738894,268101108759444694664881381420,651263621959614949504038473738,
    2806831618366465803512680386891336556491890,1185533765510123997109451099213894,554421545655550768080759038004,0,
    611096091658930148289654481007630525168366946,51559267622838291506933799063574,18541561682423726721176604516404,564609418212885505008209930,
    54570524404664017895656,8254162131202801054282774317564432394,235575413701497624248478246903860,67968036362888614536203221340170,
    2264042951599503590111680528992187578,867717375764634470977582,1241770329861532602159687802924,13565441389038271467530,
    19889111919220572602455246076811625467424239512799716324454,97076826612502096350532929064982,13783538910037763170356,5673088707373601806571971605983924234,
    0,4852105386816196888021890687307846,736683644411645646606442588,20510373785240604730,
    13529446216682075865224,1827096295224137104194801686,28229394661063922819428,94114645298006097880935232693349048089841774]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_416 : Block 17 30030 416 448 :=
  checked_packed [
    2520201136040323245261468846,5751999508222217332307914490315280394,341673050268607337124669169708,906436496986792516609118218,
    28805545561627610333368,87284769542851025531096113614862,60054768888783091718167577239596,224737188877033536993738966962202,
    132608215393637138894880409248892585265608082,0,57635066031563679473996,27964289016998075043866,
    92399034506651104054428385162666,7129357512326649198910069176012814,29381481517106258255940,79137695749776795058124623898,
    350854859265340531883934672,494643647188271717568971215240572178530,393609913572429433220433453108,648576966652859828475531290,
    14790758719302343344472,492258511420537929222590486,626731830575827737409422134091820,1082470610251123110364394199491547206,
    1131767146876050674643121470,196674038990101544139516433661159280654,0,13502354360992976042477673790473998917984324778944932612778346520983991880217209048848322793482,
    3119445719248374807833740862046392,61334007130648201982957397741582,77101847479893869176935032037428,3171366006042061802200274558389325834]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_448 : Block 17 30030 448 480 :=
  checked_packed [
    41236892494831745297291577059718330,28458266949354150368739594286,30599049944987093442972,3860347554917424560728969226,
    488978566236430766457016,386626752757221109158054507581462,1331973007993609974961938484,9240866852560132825247417413008557936624096401075444251207193150233622666004281485620833512581704053061324870,
    470448074532094704,373522110802772173336287917299165923643402,479480511408681022206506967084,0,
    1401278015499333366564041306407876156176324261680982606331972807570654,235529504873715333351870486,101900385999853399144769637064748,2896676138615875003159154738,
    11372739188863612354262594242645865970,519925812435786066292641806,2154306911981582405769109548,15803580536642003275786,
    1999972494206005516714360,258286323257062381802332379680790,30779536043735854882868,3252192845508879067689183827233607750,
    25688049582634546980820173657269630396,78098310350623953924570569581298681122970,67839807520327199662790418484,6850147426148873566818356330237962,
    0,32345353265134241321046,32423534179690148274340,738727101845965539332436529202]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_480 : Block 17 30030 480 512 :=
  checked_packed [
    7074214747299284934313655417217798,942357306991976701242508316686,32933566373333177574147090297309693841782006,254235958459642804689501687818,
    3057910929327375130069844152,9620631246309427916050470,20762511551796043124318356,2904731564877978547234829289186660362,
    39133867449211215934177741213852132492457242,4676544329585048243727845869936971846,1778953061948376566797967404,68448360394925742379715136589898,
    507566487574168040,0,547665949639925398361367126068,3254638581871621055028639141539614734,
    1270484003598009648155273997368440246,81754374754371222889681813245974,1698786272639206120728043564,16516496403350949898,
    1331059816273314391848400010,175875741289731225768796622870,280324359085372324267492909100,6350797701575870846037832527118518987226460192772106,
    31668209092484965219858837523166916,10557132837219929555996734,73317139064406348406828,53477735554510179432249954314,
    1331059816367749246534825362,33604245485961351190,0,4367010181224315842728018]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_512 : Block 17 30030 512 544 :=
  checked_packed [
    919219229868019223726404710,1525043531083625975316015300481038,949867436846219249890204640616500,1043410670933807919556602324062218,
    70677503769653081555320,2420669640732090323009113830723598,94170677831458836795250578563116,35224801169861783851042,
    9259714522351945605309705002242028802,833380735722005600122441742,538498498442567948,1760993107097284915520073633802,
    20771277737964863131685115995413980067399842411694,11078117813366880128396357742601703474,4701343155221053860374131898,0,
    34021203228961358020845572437437782344247778768364,1622270580321532514350,104063006220078831172821756944436,1854606553091749246868131866,
    2901504676288509090184911531346841368703022194,1204704207792714340742167404582193336330,185754035957469673194136805420,3453801093668340563305304114,
    17732051503336826187490312666243431216985262,241763826704307526380194746919678119812009994,838808290841160277041196,234485180468551423862051812451291162,
    557057704963621000,31179795799218681556462202788331558660841934858,161355486171524651952542937260084,146501633516160699517944597581850]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_544 : Block 17 30030 544 576 :=
  checked_packed [
    0,1533627169197237926197127418744406020106,375061192555719404520613093420,4894179371909606636351238176772122,
    2180765293302377758223415394456,101685937602563927088615691128846,10940995368401136840680375599476257906,1535878411817748476546162626610,
    7416980851066969121498366608,943072426643342543787397134,1185878932263578499178045484,572523710397812762,
    23089631717061000010312749957272,292882687460668589480087574,4797524681161140497440715138310086700,37938462323894757888082,
    1010120978612808814335899122,0,2280002041480469795037000890,303505966854990526467931686475665458,
    4897453320033106301236440102617384,13995326348380195481886426047451988570264537420404134560274348680050504250354440520070351067713966244450249639269801292205456437064765450,7730435413927865836093055028,88818431184772267649676611610,
    4864914407190272851683980435535070,3401778832238866476342183964184646,18559635604520786339100106828,1036201684777346384053407754,
    38504633153195448746120,89351913173244693970325453410318,684268230502281633390034690100,21072326725520305958742085366896922634]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_576 : Block 17 30030 576 608 :=
  checked_packed [
    185325287703270966526108208494084,1848773114805037874276889152454660166,0,564650700378960319639195658,
    5462414951782023117629961552024,3389178194069727519481124811108384357792878602,18977366295673727820505492,620667189745561951572210432872474,
    1004389033416796390734286614290667628889588642954,98008913824233536795021676558,106220389403283243362284063432756,1736328978018310124569941250058,
    1062807115132247902263170843160,1239474715818673284944236566,183685905912932212318624817204,24754476315484215366109388580017147914,
    260657856189991135092832393508026,474503627155874198851058187374606,654177390297513847682966740803628,0,
    43789415742267474072,7359923778433820736715269861514182297391114,83324770202616596537396,56233739732541201410686837348896818,
    40766301075428066984642752837052,31701021071120876188123395943728314060822,435764609133895105918270,3889225486694478409329807386,
    43488545601050236652896392,4675009989559542560373870614,2160987027779889058051444,178216767447979653164907846701082]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_608 : Block 17 30030 608 640 :=
  checked_packed [
    8854222664182356081014113502537231565337846,546177909514382946874900733156340535306,1080042996473361353142181932,89771418130785947285983242,
    0,1661721090910048388413529113184233500708914,1314031516544825187452854324,41398817492443185811490,
    3625331646216156563499150458183659011716282,118947410069955777866502206,5491581260585534713503948844,391780685040579484525149754161019635953137881158,
    14021517657769842358588852945302630,503722288758443389474308864727846926,33983913290965543475737094266924,475861305731572778352689580871706,
    101246124373385134637804886276941607560312516,144372301303347822954908290650126,1945536365316948323202472169435045932,42096584156129831948298,
    590666230117975295953815394290449218490254497613828206462911702458644215366058180325786252173755723472518090568805678711862644,0,42182544458245405155444,45564569619769366040920723490,
    457479037307585262793902,517538868505606095680699262570510,45672807759196238565613740,5393522338350914618105482294070970683406,
    446482236295026463031181640,4252924698465919227030224148495339618,3482103453421654051797390598260,93236919572488335115838952298254346]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_640 : Block 17 30030 640 672 :=
  checked_packed [
    31303468730730501805796263740877030482578350916017075458,182423083063272498662472582959126,481633699018659816234708639796,3959367726830783322044502026,
    378385762419701020162175863579751562,5226289275299517602329079322775574,0,7749697305827682851876604697066344458,
    26979550324656472878261317377880931128094447975662609290524140,43937179475796327141438,6138774436439729338450976812,189987626232269888729018758336522,
    88977813458765215711528,3584919426223443097628614594582,923330673594767536364771560398892,150231995230028080643870761685018,
    4316643615341823089446463559305092581825578022206,8472903825786508795416691228020806,101535025423326264718163714092,10847960967692152336588546950289409708102,
    5505345936193655615514493064,82431100715956310428635203899462,400111098746341080420405223468,0,
    3920863225731854822768402480789044,207671410887472812710467372847118,14459334044315029983994508,621095437450003717206052874,
    47358022639012149731573331306673757864565185456604460134,317232288771288562137839717998137358,260657856190157568924392846537842,2318924802214350680423697642101705543694]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_672 : Block 17 30030 672 704 :=
  checked_packed [
    65778072493448044298523757278772,39865988379449864753166,4140405136267289484764710445132,659754728347691327802052618,
    19511855520866649395937624602526538522440818,403866008620086300970293767654346766,44001566903030721031116947464244,2271610310854378799526234306380275126298,
    0,46102763799262569435198,360271132675475594436157484,68472878232001468814732562442,
    1923057055117464792029904571323419052766580,206150744168510786820172324802574,503840303287251214917154381868,32498424599817867328301706192705556490,
    47006722120080711076120151717043989656978,2017015305183314535973489430750192562344034,158258155577475519295219092693044,2565875326508733316153559943745562,
    17135462448471593801169780968,15357362061113102545047087090539433994,451212702833983845778333748,30242970960212459604932363087253530,
    156355325323047791560728019632,0,15981665917588824846770252,3216010478210525170118098245862297670,
    7803309544954209918630510888,8421900973379179994825252418662,582220234786627839972155479564340,254846593203623848725086780526618]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_704 : Block 17 30030 704 736 :=
  checked_packed [
    101802656142285649855416421317551387943384238,3233757238124417090122028143539671535630,939629201036023678338807833305132,1077110993211917431632212004890,
    47673885091396640063672,169924472706982306640328816332822,637953197955896870760187724570668,53956476560192292600745800341917706,
    3013809432478884033768469618,819106273844997891735687214,0,5544621685507496690183049242,
    35828754193828929958177195180184,24537662279955056595825816525543135252494,879082299971327870345648575356972,5634171020961539504447781442764673094,
    21202493555441255455995757136,3026663434838633092345794937229326,1928383427939289226748443630772276,1285999952777970480576466954,
    85054984227594474609638925131071894642,3888213485633090801215840718870,47540413960654080188468,331111268630643818883053595549241394,
    600046377437737868169683505634510278505646,776508396016156065166776707584014,741811537235269847665143952973876,0,
    237168912088625606301722214672659948,109949240193347296764892373472776206,4992788439437278131863434378,1039744502799589065095952805662746]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_736 : Block 17 30030 736 768 :=
  checked_packed [
    5682248629264632697979892182037762,46394667916433271140348355701085573130,1158182430829739529162764861841892,1358021259497136742993930,
    1049030922662149506881044632,4030610012730806064727986246,165972668232517329914034746929717292,19200060667467176450779909453737103430,
    892317524448670155192673221993934454996121820362100,98818891107237979178354024035693832739753994,9038710674111286395577311276,16588767249651241840545818,
    0,4011212508813597989688823517206,1695461301687174294928189097517100,1071128725525948142719026,
    4092308214738328027866982869948390548850095602,691276362545946939101198,7228725861186939591921493830803500,261009086108032426429873066610714,
    114046249667594181153210916206636745925346,8572864693123488418345294965117412544876554,51469484913804026322996,173234133121486391220411851345946,
    111042067430524353727158162008472205452669646460,155431388519707383865746879680526,107941749121137778732,14922509396696950623236898701784911886,
    159186301737676183985031120913708314,0,217989847682167662796890563420204,34390396839696096229116689403208536074]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_768 : Block 17 30030 768 800 :=
  checked_packed [
    32598274991116644902315120362816176,95041657453466809898775875598,117001119290593783235899634943008016828912814273674,8785460446878121232113697294389258,
    208767243804621064388792,1183821749124454283420373062,1341445736150107766661172,900877702979531185334834399547494410,
    12586306018835839811492775410546090,11882398824674330185671344998322246,62566672670455651313399762002092,8728055461737514159761787709221244938,
    51304033099994917519656,318614407359886854884542812000326,0,900325140110676668188711417024538,
    7907058289904519032490086037992634,8107454193156857516019153678389743638,797893064639621165793920088547372,44869925186085418126350639300645274783814,
    231033557833911759844013670221875909735915959437265308102216922250,209376349874052852409941199163462,1239790550247703447633921589649452,2619272694578089027963537244540343685134,
    52937998559201460257360,3614750423979675326399522713636878,53768396597343943663660,425772321639576261643030499338,
    979429668154954195341335086891170751531475479311834,132337198526638935952093833958874969771347978,176212753596941227170159687028,0]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_800 : Block 17 30030 800 832 :=
  checked_packed [
    54609599212901342687830442390762929451464052,4056855481156686624401133582,6943016005194168966062172,4357622813413156129932840970,
    4150901601183420740642818435858568,4555306503019786335133206008546739991089166,563552857643144287134687284,1321966174685938859785694803793023046,
    17654120168361392298757671465735574321417094227309682,35156828373860785025178760815733994686368930861126,805809340707992475364850493562924,2907299846730192767697156190216942906249230,
    49419367489601652364637153998039011680411357033574,3521764930426912119319253156368406,6747673861211208587220623412,15769391810093362738805042931830810,
    0,6410572936058855887999086,47606319807271197632402573535427223417256285320294,1164109509404113942614026,
    5801254563379437004621103288,631653537971220316653480841238,10034593950946065129588,1060027240197037891701012697114,
    1179310375378967485310057958663533922,5871946520474839426378902802478,56012885015230253375532,1047566792568078341861686644746,
    13216349328250634516477131704254840,206685171901903146114217351843854,31411151725556660582366438236404,454264701028574853197058805786]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_832 : Block 17 30030 832 864 :=
  checked_packed [
    169004896407076530664336280464408424415202753131706,0,42929642791016365916650578386988,5469042911097915229218017306,
    6050252964302252945530958950,1349237567297462253234688070,90557201775455725230906941652,371197085559285100781654842446274552148267022,
    3492042097753220514572173904,3966424594506175261023044621784059954,9566468304661832583604084780,992280738905855891374269695791114,
    20414443929203995488305384,24476818334051656310115931664515338250,861031988818106463861157666868,3523283568491763558788414195880711635138936923488208895325587244278116311382917434155900793334047704732196340240394,
    57937965955267778186321863586624686,10185795804201770464216879166,0,898063247522722157221080207386,
    1035592668341506954407985288,57533168470586826962022,4095982930079314652115229210583084,232625217149969780183637430370,
    52585186668954383382754958,47122401511891124050368305713261842442,116341778079378038595820,1194293316067428067804231095029770,
    117070399223200489685128,107622726027137090347601942,1225672902406525208604755107892,4429752584961732809633152592052819595278]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_864 : Block 17 30030 864 896 :=
  checked_packed [
    8781609246167970453909439120,4353202643020776631199894687715342,236769514311910630105180,0,
    13053618039215907602120212036238455994,5346706202958095962400100374,853904323520886111198410448940,54273984919080812941410,
    10828765748432591351313323647841526,218929895418630358368893697789966,3873058243708633353151324204,439736805569643344156464848664793098,
    119030173606172549988584,15961303792358467127293775894,4150901601183642859693766395043956,8827323939022019526732892929527858,
    62001858816868223764859591797519834,232625217150141250396378632206,705142939626869101841468104756,139253434259323020644362,
    0,121228071128898730015777099798,7627034168975267238780980,58971710487820679482203473944132980750,
    15071700844902184066424814520176485030983028,121873911172532388499550,1150188927687257716083477232754740,73972826612060836873134674050,
    31224732842647194628538504,12523211512541119254550,325016502121794275265525191811116,4770637095040578127168548567519258]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_17_896 : Block 17 30030 896 902 :=
  checked_packed [
    33028281098834783215668782606097331338,20667841980505960562991046398580594053130,3518809527926602809589757219184692,1584456834457863002016190522,
    1297807065491207072187135587022388,0]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_19_0 : Block 19 510510 0 32 :=
  checked_packed [
    0,6692685059050773671397298186,8761810589065308,1806742590809913486741530,
    17523621182324920,8802493703379886026048495685642,14218115452431460823212084,1817344641377526740749570281482,
    9229950603411465450718,91252759647737748764465851472547850,31070305056077788357278572596,18862442773683571159430336522,
    34994139904183005066767953729451452,4316734288571682824806809473038,306948003618124682630275220,6000964152885592722645041811482,
    31849297110475871221715055790,695079424397325457428494,183055594433532845134083792940,0,
    669280305582121407741965570,1351188950294758945466658661924039898959882,18343257154496077606214581746671660,34289574772870800740386,
    27819680756987729052304,5639214907080814702609311993870,14920200370315444887596,157675354003895725194069777813530597371391512646,
    7221903521139825619240088212119393983154488357990,976931791154261327460962326,486985211805754727617239537688620,45282858840606028767832144802222090]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_19_32 : Block 19 510510 32 64 :=
  checked_packed [
    3262836224453618389624170477549108,30548443609956437805510678286398,5215474998287831502058666527301684,9175604163806997890609334606184321074,
    40523897186118682034424,7536369305380533569397399220524158986,0,1594693375782510620715434134957996380230,
    178967948278318513692636676,28666814812724958402760190033691414538,22139881949734786529463640396,99774648959675966427194,
    4608055023556484601466601608,104175147077182766977046,876940128757388886477452087402540,333583257054623266678001621660882271675093002,
    2797078666712201029379092700720103262549364,49736633446851503600337557739540550,897194093313981602997518111038518494,4168561663004091727952744458,
    39427775759654612367608660104,99060777793119322385965883760150843406,814893432082614512921682158559300,33421315238737585891184674,
    13009908672062132598313472727289655799592194,0,7749986942571705398143754284,705492754409932449170591770,
    1056628600668459433036103816,13850279768265984695689924442136227352586,364357403193613182981809635336244,1234792807874149668506600214562]
    (by decide +kernel) (by decide +kernel)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_19_64 : Block 19 510510 64 67 :=
  checked_packed [
    86882982122699709314620487226895835870562,168422699207539073433601419750936598,7453186852121080473152212099407924]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem block_23_0 : Block 23 9699690 0 6 :=
  checked_packed [
    0,190441407911158761951287296508563526,5922964987760320066428623938134084,188230168334064848983368136658966,
    17617464873217246432049787635350123622,67570836634413038389083295426937884686]
    (by decide +kernel) (by decide +kernel)


end PracticalComplements.FiniteProof

namespace PracticalComplements.FiniteProof


set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_0 : Block 0 1 0 36 := (join_blocks block_0_0 block_0_32)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_3 : Block 3 2 0 450 := (join_blocks (join_blocks (join_blocks (join_blocks block_3_0 block_3_32) (join_blocks block_3_64 block_3_96)) (join_blocks (join_blocks block_3_128 block_3_160) (join_blocks block_3_192 block_3_224))) (join_blocks (join_blocks (join_blocks block_3_256 block_3_288) (join_blocks block_3_320 block_3_352)) (join_blocks (join_blocks block_3_384 block_3_416) block_3_448)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_3 {n : ℕ} (hn : qualifies n)
    (hd : primorial (3-1) ∣ n) (hp : ¬3∣n)
    (hb : n<4*3^2*(2+3)^2) : n∈known := by
  have hv : primorial (3-1) = 2 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_3 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_5 : Block 5 6 0 2017 := (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block_5_0 block_5_32) (join_blocks block_5_64 block_5_96)) (join_blocks (join_blocks block_5_128 block_5_160) (join_blocks block_5_192 block_5_224))) (join_blocks (join_blocks (join_blocks block_5_256 block_5_288) (join_blocks block_5_320 block_5_352)) (join_blocks (join_blocks block_5_384 block_5_416) (join_blocks block_5_448 block_5_480)))) (join_blocks (join_blocks (join_blocks (join_blocks block_5_512 block_5_544) (join_blocks block_5_576 block_5_608)) (join_blocks (join_blocks block_5_640 block_5_672) (join_blocks block_5_704 block_5_736))) (join_blocks (join_blocks (join_blocks block_5_768 block_5_800) (join_blocks block_5_832 block_5_864)) (join_blocks (join_blocks block_5_896 block_5_928) (join_blocks block_5_960 block_5_992))))) (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block_5_1024 block_5_1056) (join_blocks block_5_1088 block_5_1120)) (join_blocks (join_blocks block_5_1152 block_5_1184) (join_blocks block_5_1216 block_5_1248))) (join_blocks (join_blocks (join_blocks block_5_1280 block_5_1312) (join_blocks block_5_1344 block_5_1376)) (join_blocks (join_blocks block_5_1408 block_5_1440) (join_blocks block_5_1472 block_5_1504)))) (join_blocks (join_blocks (join_blocks (join_blocks block_5_1536 block_5_1568) (join_blocks block_5_1600 block_5_1632)) (join_blocks (join_blocks block_5_1664 block_5_1696) (join_blocks block_5_1728 block_5_1760))) (join_blocks (join_blocks (join_blocks block_5_1792 block_5_1824) (join_blocks block_5_1856 block_5_1888)) (join_blocks (join_blocks block_5_1920 block_5_1952) (join_blocks block_5_1984 block_5_2016))))))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_5 {n : ℕ} (hn : qualifies n)
    (hd : primorial (5-1) ∣ n) (hp : ¬5∣n)
    (hb : n<4*5^2*(8+3)^2) : n∈known := by
  have hv : primorial (5-1) = 6 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_5 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_7 : Block 7 30 0 1105 := (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block_7_0 block_7_32) (join_blocks block_7_64 block_7_96)) (join_blocks (join_blocks block_7_128 block_7_160) (join_blocks block_7_192 block_7_224))) (join_blocks (join_blocks (join_blocks block_7_256 block_7_288) (join_blocks block_7_320 block_7_352)) (join_blocks (join_blocks block_7_384 block_7_416) (join_blocks block_7_448 block_7_480)))) (join_blocks (join_blocks (join_blocks (join_blocks block_7_512 block_7_544) (join_blocks block_7_576 block_7_608)) (join_blocks (join_blocks block_7_640 block_7_672) (join_blocks block_7_704 block_7_736))) (join_blocks (join_blocks (join_blocks block_7_768 block_7_800) (join_blocks block_7_832 block_7_864)) (join_blocks (join_blocks block_7_896 block_7_928) (join_blocks block_7_960 block_7_992))))) (join_blocks (join_blocks block_7_1024 block_7_1056) block_7_1088))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_7 {n : ℕ} (hn : qualifies n)
    (hd : primorial (7-1) ∣ n) (hp : ¬7∣n)
    (hb : n<4*7^2*(10+3)^2) : n∈known := by
  have hv : primorial (7-1) = 30 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_7 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_11 : Block 11 210 0 3156 := (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block_11_0 block_11_32) (join_blocks block_11_64 block_11_96)) (join_blocks (join_blocks block_11_128 block_11_160) (join_blocks block_11_192 block_11_224))) (join_blocks (join_blocks (join_blocks block_11_256 block_11_288) (join_blocks block_11_320 block_11_352)) (join_blocks (join_blocks block_11_384 block_11_416) (join_blocks block_11_448 block_11_480)))) (join_blocks (join_blocks (join_blocks (join_blocks block_11_512 block_11_544) (join_blocks block_11_576 block_11_608)) (join_blocks (join_blocks block_11_640 block_11_672) (join_blocks block_11_704 block_11_736))) (join_blocks (join_blocks (join_blocks block_11_768 block_11_800) (join_blocks block_11_832 block_11_864)) (join_blocks (join_blocks block_11_896 block_11_928) (join_blocks block_11_960 block_11_992))))) (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block_11_1024 block_11_1056) (join_blocks block_11_1088 block_11_1120)) (join_blocks (join_blocks block_11_1152 block_11_1184) (join_blocks block_11_1216 block_11_1248))) (join_blocks (join_blocks (join_blocks block_11_1280 block_11_1312) (join_blocks block_11_1344 block_11_1376)) (join_blocks (join_blocks block_11_1408 block_11_1440) (join_blocks block_11_1472 block_11_1504)))) (join_blocks (join_blocks (join_blocks (join_blocks block_11_1536 block_11_1568) (join_blocks block_11_1600 block_11_1632)) (join_blocks (join_blocks block_11_1664 block_11_1696) (join_blocks block_11_1728 block_11_1760))) (join_blocks (join_blocks (join_blocks block_11_1792 block_11_1824) (join_blocks block_11_1856 block_11_1888)) (join_blocks (join_blocks block_11_1920 block_11_1952) (join_blocks block_11_1984 block_11_2016)))))) (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block_11_2048 block_11_2080) (join_blocks block_11_2112 block_11_2144)) (join_blocks (join_blocks block_11_2176 block_11_2208) (join_blocks block_11_2240 block_11_2272))) (join_blocks (join_blocks (join_blocks block_11_2304 block_11_2336) (join_blocks block_11_2368 block_11_2400)) (join_blocks (join_blocks block_11_2432 block_11_2464) (join_blocks block_11_2496 block_11_2528)))) (join_blocks (join_blocks (join_blocks (join_blocks block_11_2560 block_11_2592) (join_blocks block_11_2624 block_11_2656)) (join_blocks (join_blocks block_11_2688 block_11_2720) (join_blocks block_11_2752 block_11_2784))) (join_blocks (join_blocks (join_blocks block_11_2816 block_11_2848) (join_blocks block_11_2880 block_11_2912)) (join_blocks (join_blocks block_11_2944 block_11_2976) (join_blocks block_11_3008 block_11_3040))))) (join_blocks (join_blocks block_11_3072 block_11_3104) block_11_3136)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_11 {n : ℕ} (hn : qualifies n)
    (hd : primorial (11-1) ∣ n) (hp : ¬11∣n)
    (hb : n<4*11^2*(34+3)^2) : n∈known := by
  have hv : primorial (11-1) = 210 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_11 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_13 : Block 13 2310 0 446 := (join_blocks (join_blocks (join_blocks (join_blocks block_13_0 block_13_32) (join_blocks block_13_64 block_13_96)) (join_blocks (join_blocks block_13_128 block_13_160) (join_blocks block_13_192 block_13_224))) (join_blocks (join_blocks (join_blocks block_13_256 block_13_288) (join_blocks block_13_320 block_13_352)) (join_blocks block_13_384 block_13_416)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_13 {n : ℕ} (hn : qualifies n)
    (hd : primorial (13-1) ∣ n) (hp : ¬13∣n)
    (hb : n<4*13^2*(36+3)^2) : n∈known := by
  have hv : primorial (13-1) = 2310 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_13 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_17 : Block 17 30030 0 902 := (join_blocks (join_blocks (join_blocks (join_blocks (join_blocks block_17_0 block_17_32) (join_blocks block_17_64 block_17_96)) (join_blocks (join_blocks block_17_128 block_17_160) (join_blocks block_17_192 block_17_224))) (join_blocks (join_blocks (join_blocks block_17_256 block_17_288) (join_blocks block_17_320 block_17_352)) (join_blocks (join_blocks block_17_384 block_17_416) (join_blocks block_17_448 block_17_480)))) (join_blocks (join_blocks (join_blocks (join_blocks block_17_512 block_17_544) (join_blocks block_17_576 block_17_608)) (join_blocks (join_blocks block_17_640 block_17_672) (join_blocks block_17_704 block_17_736))) (join_blocks (join_blocks (join_blocks block_17_768 block_17_800) (join_blocks block_17_832 block_17_864)) block_17_896)))

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_17 {n : ℕ} (hn : qualifies n)
    (hd : primorial (17-1) ∣ n) (hp : ¬17∣n)
    (hb : n<4*17^2*(150+3)^2) : n∈known := by
  have hv : primorial (17-1) = 30030 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_17 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_19 : Block 19 510510 0 67 := (join_blocks (join_blocks block_19_0 block_19_32) block_19_64)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_19 {n : ℕ} (hn : qualifies n)
    (hd : primorial (19-1) ∣ n) (hp : ¬19∣n)
    (hb : n<4*19^2*(150+3)^2) : n∈known := by
  have hv : primorial (19-1) = 510510 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_19 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem all_23 : Block 23 9699690 0 6 := block_23_0

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
private theorem class_23 {n : ℕ} (hn : qualifies n)
    (hd : primorial (23-1) ∣ n) (hp : ¬23∣n)
    (hb : n<4*23^2*(156+3)^2) : n∈known := by
  have hv : primorial (23-1) = 9699690 := by decide +kernel
  rw [hv] at hd
  obtain ⟨j,rfl⟩ := hd
  exact all_23 j (by omega) (by omega) hn hp

set_option maxRecDepth 32768 in
set_option maxHeartbeats 8000000 in
theorem known_of_shape {n : ℕ} (hn : qualifies n)
    (h : (Odd n ∧ n<36) ∨ ∃ ph : ℕ × ℕ, ph ∈
      [(3,2),(5,8),(7,10),(11,34),(13,36),(17,150),(19,150),(23,156)] ∧
      primorial (ph.1-1)∣n ∧ ¬ph.1∣n ∧ n<4*ph.1^2*(ph.2+3)^2) : n∈known := by
  rcases h with hs|⟨ph,hm,hd,hp,hb⟩
  · simpa using all_0 n (by omega) hs.2 (by simpa using hn)
      (by simp only [one_mul,zero_dvd_iff]; have := hn.1; omega)
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    · exact class_3 hn hd hp hb
    · exact class_5 hn hd hp hb
    · exact class_7 hn hd hp hb
    · exact class_11 hn hd hp hb
    · exact class_13 hn hd hp hb
    · exact class_17 hn hd hp hb
    · exact class_19 hn hd hp hb
    · exact class_23 hn hd hp hb

end PracticalComplements.FiniteProof

theorem OMA.solution : type_of% @OMA.S_oeis_a321152.main := by
  intro n
  rw [PracticalComplements.term_iff_qualifies]
  exact ⟨fun hn => PracticalComplements.FiniteProof.known_of_shape hn
    (PracticalComplements.finite_shape hn), PracticalComplements.FiniteProof.known_qualifies n⟩
