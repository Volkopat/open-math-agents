import OMAStatements.S_oeis_a294225
import Mathlib.Data.Nat.Totient
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.List.Nodup
import Mathlib.Algebra.GCDMonoid.Nat
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum.Prime

/-! # Infinitely many practical triples of the form q, q+2, q²+2

The exponent construction, its conventional proof and two independent seed verifiers are at
https://github.com/Krgrocon/open-math-agents/tree/c6b510f5a8dc9b3ce5b02eff71f33b79ad123531/research/oeis-a294225 .
The practical component lemmas were first used in our proof of A321152.
Problem proposed by Zhi-Wei Sun, https://oeis.org/A294225 .
-/

section
namespace PracticalTriples

/-- Each weight can exceed the sum of the preceding weights by at most three. -/
def Gap (w : ℕ → ℕ) : ℕ → List ℕ → Prop
  | _, [] => True
  | s, d :: ds => w d ≤ s+3 ∧ Gap w (s+w d) ds

def Ordered (N : ℕ) : Prop :=
  ∃ ds : List ℕ, ds.Nodup ∧ ds.toFinset = N.divisors ∧
    4*ds.length ≤ N ∧ Gap Nat.totient 0 ds

theorem gap_append {w : ℕ → ℕ} {s : ℕ} {ds ts : List ℕ}
    (h : Gap w s ds) (ht : Gap w (s+(ds.map w).sum) ts) : Gap w s (ds++ts) := by
  induction ds generalizing s with
  | nil => simpa using ht
  | cons d ds ih =>
    exact ⟨h.1, ih h.2 (by simpa [Nat.add_assoc] using ht)⟩

theorem gap_scaled {w v f : ℕ → ℕ} {s z c : ℕ} {ds : List ℕ}
    (h : Gap w s ds) (hbudget : c*(s+3) ≤ z+3)
    (hf : ∀ d ∈ ds, v (f d) = c*w d) : Gap v z (ds.map f) := by
  induction ds generalizing s z with
  | nil => trivial
  | cons d ds ih =>
    have hd := hf d (by simp)
    constructor
    · rw [hd]
      exact (Nat.mul_le_mul_left c h.1).trans hbudget
    · apply ih h.2 _ (fun i hi => hf i (by simp [hi]))
      rw [hd, Nat.add_right_comm s (w d) 3, Nat.mul_add]
      omega

/-- Given an initial product, append factors known only through factor-of-four
bounds on their sizes. The power budget pays for both bounds at every step. -/
theorem append_factors {P : ℕ → Prop}
    (close : ∀ {m f : ℕ}, P m → 0 < m → 0 < f → f ≤ 2*m → P (m*f))
    {ds : List ℕ} {w F : ℕ → ℕ} {B c s h m : ℕ} (hm : P m) (hm0 : 0 < m)
    (hg : Gap w s ds) (budget : 3*c+2*(h+ds.length) ≤ B)
    (inv : 2*2^(B+c*s) ≤ m*2^(2*h))
    (bounds : ∀ d ∈ ds, 2^(c*w d) ≤ 4*F d ∧ F d ≤ 4*2^(c*w d)) :
    P (m*(ds.map F).prod) := by
  induction ds generalizing s h m with
  | nil => simpa using hm
  | cons d ds ih =>
    obtain ⟨lo,hi⟩ := bounds d (by simp)
    have wd := Nat.mul_le_mul_left c hg.1
    rw [Nat.mul_add] at wd
    simp only [List.length_cons] at budget
    have deg : c*w d+2*h ≤ B+c*s := by omega
    have pos : 0 < F d := by
      have : 0 < (2:ℕ)^(c*w d) := by positivity
      omega
    have small : F d ≤ 2*m := by
      refine Nat.le_of_mul_le_mul_right ?_ (show 0 < (2:ℕ)^(2*h) by positivity)
      calc
        F d * 2^(2*h) ≤ (4*2^(c*w d))*2^(2*h) := Nat.mul_le_mul_right _ hi
        _ = 4*2^(c*w d+2*h) := by rw [pow_add]; ring
        _ ≤ 4*2^(B+c*s) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) deg)
        _ ≤ (2*m)*2^(2*h) := by
          simpa only [← Nat.mul_assoc] using Nat.mul_le_mul_left 2 inv
    have next : 2*2^(B+c*(s+w d)) ≤ (m*F d)*2^(2*(h+1)) := by
      calc
        2*2^(B+c*(s+w d)) = (2*2^(B+c*s))*2^(c*w d) := by
          rw [Nat.mul_add, ← Nat.add_assoc, pow_add]; ring
        _ ≤ (m*2^(2*h))*(4*F d) := Nat.mul_le_mul inv lo
        _ = (m*F d)*2^(2*(h+1)) := by
          rw [show 2*(h+1)=2*h+2 by omega, pow_add]; ring
    have step := ih (h := h+1) (close hm hm0 pos small) (Nat.mul_pos hm0 pos) hg.2
      (by omega) next (fun i hi' => bounds i (by simp [hi']))
    simpa only [List.map_cons, List.prod_cons, Nat.mul_assoc] using step

end PracticalTriples
end

section
namespace PracticalTriples

/-- Append the divisors with exact new prime exponent in the order induced by
the original divisor list. The lists can use any order. -/
theorem divisor_layer {N p e : ℕ} {old ds : List ℕ}
    (hp : p.Prime) (hN : N ≠ 0) (hpN : ¬ p ∣ N)
    (ho : old.Nodup ∧ old.toFinset = (N*p^e).divisors)
    (hd : ds.Nodup ∧ ds.toFinset = N.divisors) :
    (old ++ ds.map (fun d => d*p^(e+1))).Nodup ∧
    (old ++ ds.map (fun d => d*p^(e+1))).toFinset = (N*p^(e+1)).divisors := by
  have old_iff (x : ℕ) : x ∈ old ↔ x ∣ N*p^e := by
    rw [← List.mem_toFinset, ho.2, Nat.mem_divisors]
    simp [hN, hp.ne_zero]
  have ds_iff (x : ℕ) : x ∈ ds ↔ x ∣ N := by
    rw [← List.mem_toFinset, hd.2, Nat.mem_divisors]
    simp [hN]
  constructor
  · apply ho.1.append
    · exact hd.1.map (fun _ _ h => (mul_left_inj' (pow_ne_zero _ hp.ne_zero)).mp h)
    · intro x hx hnew
      obtain ⟨d, _, rfl⟩ := List.mem_map.mp hnew
      have hpow : p^(e+1) ∣ N*p^e :=
        (dvd_mul_left _ _).trans ((old_iff _).mp hx)
      apply hpN
      apply (mul_dvd_mul_iff_right (pow_ne_zero e hp.ne_zero)).mp
      simpa only [pow_succ'] using hpow
  · ext x
    have hnext : N*p^(e+1) ≠ 0 := mul_ne_zero hN (pow_ne_zero _ hp.ne_zero)
    simp only [List.mem_toFinset, List.mem_append, List.mem_map, Nat.mem_divisors, old_iff, ds_iff]
    constructor
    · rintro (h | ⟨d, hdN, rfl⟩)
      · exact ⟨h.trans (mul_dvd_mul_left N (pow_dvd_pow p (Nat.le_succ e))), hnext⟩
      · exact ⟨mul_dvd_mul_right hdN _, hnext⟩
    · intro h
      obtain ⟨d, t, hdN, ht, rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h.1
      obtain ⟨j, hj, rfl⟩ := (Nat.dvd_prime_pow hp).mp ht
      by_cases he : j = e+1
      · exact Or.inr ⟨d, hdN, by rw [he]⟩
      · exact Or.inl (Nat.mul_dvd_mul hdN (pow_dvd_pow p (by omega)))

end PracticalTriples
end

section
namespace PracticalTriples

private theorem divisor_degree {N : ℕ} {l : List ℕ}
    (hl : l.Nodup) (hset : l.toFinset=N.divisors) : (l.map Nat.totient).sum=N := by
  rw [← List.sum_toFinset Nat.totient hl, hset, Nat.sum_totient]

private theorem divisor_value {V : ℕ → ℕ}
    (product : ∀ {n : ℕ}, Odd n → ∏ d ∈ n.divisors, V (2*d) = 2^n+1)
    {N : ℕ} (hN : Odd N) {l : List ℕ}
    (hl : l.Nodup) (hset : l.toFinset=N.divisors) :
    (l.map (fun d => V (2*d))).prod = 2^N+1 := by
  rw [← List.prod_toFinset _ hl, hset, product hN]

/-- Adjoining an entire new odd prime power preserves the divisor ordering and
the practicality of twice the associated Fermat-type number. -/
theorem extend_for_property {P : ℕ → Prop} {V : ℕ → ℕ}
    (size : ∀ n : ℕ, 0 < n → 2^n.totient ≤ 4*V n ∧ V n ≤ 4*2^n.totient)
    (product : ∀ {n : ℕ}, Odd n → ∏ d ∈ n.divisors, V (2*d) = 2^n+1)
    (close : ∀ {m j : ℕ}, P m → 0 < m → 0 < j → j ≤ 2*m → P (m*j))
    {N p : ℕ} (hN : Odd N) (hO : Ordered N)
    (hQ : P (2*(2^N+1))) (hp : p.Prime) (hp2 : p ≠ 2) (hnew : ¬ p ∣ N)
    (hsize : 6*(p-1) ≤ N) (e : ℕ) :
    Ordered (N*p^e) ∧ P (2*(2^(N*p^e)+1)) := by
  obtain ⟨ds,hds,hs,hlen,hgap⟩ := hO
  have hn0 : N ≠ 0 := by rintro rfl; exact (by decide : ¬ Odd 0) hN
  have po := hp.odd_of_ne_two hp2
  have pc := hp.coprime_iff_not_dvd.mpr hnew
  have dvdN {d : ℕ} (hd : d ∈ ds) : d ∣ N :=
    (Nat.mem_divisors.mp (hs ▸ List.mem_toFinset.mpr hd)).1
  induction e with
  | zero =>
    simpa only [pow_zero, Nat.mul_one] using And.intro
      (show Ordered N from ⟨ds,hds,hs,hlen,hgap⟩) hQ
  | succ e ih =>
    obtain ⟨⟨old,hold,hos,holen,hogap⟩,hprev⟩ := ih
    let B := N*p^e
    let c := p^e*(p-1)
    let f := fun d : ℕ => d*p^(e+1)
    let F := fun d : ℕ => V (2*f d)
    have Bodd : Odd B := hN.mul po.pow
    have Nle : N ≤ B := Nat.le_mul_of_pos_right N (pow_pos hp.pos _)
    have Bnext : N*p^(e+1) = B*p := by simp only [B, pow_succ, Nat.mul_assoc]
    have budget : 6*c ≤ B := by
      simpa only [c,B,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using
        Nat.mul_le_mul_right (p^e) hsize
    have bsize : 3*c+2*ds.length ≤ B := by omega
    have weight (d : ℕ) (hd : d ∈ ds) : (f d).totient=c*d.totient := by
      have cop := (pc.symm.coprime_dvd_left (dvdN hd)).pow_right (e+1)
      simp only [f,c,Nat.totient_mul cop,Nat.totient_prime_pow_succ hp,Nat.mul_comm]
    have values (d : ℕ) (hd : d ∈ ds) :
        2^(c*d.totient) ≤ 4*F d ∧ F d ≤ 4*2^(c*d.totient) := by
      have fo : Odd (f d) := (hN.of_dvd_nat (dvdN hd)).mul po.pow
      have fpos : 0 < f d := by obtain ⟨t,ht⟩ := fo; omega
      simpa only [F,Nat.totient_two_mul_of_odd fo,weight d hd] using
        size (2*f d) (by omega)
    obtain ⟨hnewlist,hnewset⟩ := divisor_layer hp hn0 hnew ⟨hold,hos⟩ ⟨hds,hs⟩
    constructor
    · refine ⟨old ++ ds.map f,hnewlist,hnewset,?_,?_⟩
      · simp only [List.length_append,List.length_map]
        rw [Bnext]
        change 4*old.length ≤ B at holen
        have h2 : 2*B ≤ B*p := by
          simpa only [Nat.mul_comm] using (Nat.mul_le_mul_left B hp.two_le)
        omega
      · apply gap_append hogap
        rw [divisor_degree hold hos, Nat.zero_add]
        exact gap_scaled (s := 0) hgap (by change c*(0+3) ≤ B+3; omega) weight
    · have hprod := append_factors (P := P) close (h := 0) (s := 0)
          (B := B) hprev (by positivity) hgap (by simpa using bsize)
          (by simp [B]) values
      have oldprod := divisor_value product Bodd hold hos
      have newprod := divisor_value product (hN.mul (po.pow (n := e+1))) hnewlist hnewset
      change ((old ++ ds.map f).map (fun d => V (2*d))).prod = _ at newprod
      rw [List.map_append,List.prod_append,oldprod,List.map_map] at newprod
      change (2^B+1)*(ds.map F).prod = _ at newprod
      rw [← newprod, ← Nat.mul_assoc]
      exact hprod

end PracticalTriples
end

section
namespace PracticalComplements

/-- The subset-sum definition of Nat.IsPractical, written with Mathlib Finsets. -/
def practical (n : ℕ) : Prop :=
  ∀ m, m ≤ n → ∃ s : Finset ℕ, s ⊆ n.divisors ∧ m = ∑ i ∈ s, i

end PracticalComplements
end

section
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
end

section
namespace PracticalTriples

open PracticalComplements ArithmeticFunction
open scoped ArithmeticFunction.sigma

theorem twice_le_sigma_succ {m : ℕ} (hm : practical m) (hm0 : 0 < m) :
    2*m ≤ σ 1 m+1 := by
  obtain ⟨s, hs, he⟩ := hm (m-1) (by omega)
  have hi : m ∉ s := by
    intro h
    have := Finset.single_le_sum (f := fun i : ℕ => i) (fun i _ => Nat.zero_le i) h
    omega
  have hsub : insert m s ⊆ m.divisors :=
    Finset.insert_subset (Nat.mem_divisors.mpr ⟨dvd_rfl,hm0.ne'⟩) hs
  have hle := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun i : ℕ => i) (by intros; omega)
  rw [Finset.sum_insert hi, ← ArithmeticFunction.sigma_one_apply] at hle
  omega

theorem mul_double {m j : ℕ} (hm : practical m) (hm0 : 0 < m) (hj : 0 < j)
    (h : j ≤ 2*m) : practical (m*j) := by
  by_contra hnot
  obtain ⟨c,b,hcb,hbig,hcop,hrough⟩ :=
    has_practical_component (Nat.mul_pos hm0 hj) (fun hh => hnot hh.2)
  have hc : 0 < c := by by_contra! hz; simp_all
  have hmc : m ∣ c := practical_divisor_dvd_prefix hc ⟨hm0,hm⟩
    (hcb ▸ dvd_mul_right m j) hrough
  have hjs : j ≤ σ 1 c+1 := by
    obtain ⟨k,hk⟩ := hmc
    by_cases he : k=1
    · have e : c=m := by simpa [he] using hk
      exact e ▸ h.trans (twice_le_sigma_succ hm hm0)
    · have hge : 2≤k := by
        by_cases hz : k=0
        · simp_all
        · omega
      have hmul := Nat.mul_le_mul_left m hge
      have := whole_le_sigma hc
      omega
  have hcop' : (m*j).Coprime b :=
    (Nat.Coprime.coprime_dvd_left hmc hcop).mul_left (coprime_to_tail hj hjs hrough)
  have hd : b ∣ m*j := hcb.symm ▸ dvd_mul_left b c
  have e := hcop'.gcd_eq_one
  rw [Nat.gcd_eq_right hd] at e
  omega

end PracticalTriples
end

section
namespace PracticalTriples
open Finset Polynomial
open scoped ArithmeticFunction.Moebius

noncomputable section

def cycloValue (h : ℕ) : ℕ := ((cyclotomic h ℤ).eval 2).toNat

private theorem cast_cycloValue (h : ℕ) : (cycloValue h : ℤ) = (cyclotomic h ℤ).eval 2 :=
  Int.toNat_of_nonneg (cyclotomic_nonneg h (by norm_num))

theorem cycloValue_pos (h : ℕ) : 0 < cycloValue h := by
  have hp := cyclotomic_pos' h (show (1 : ℤ) < 2 by norm_num)
  rw [← cast_cycloValue] at hp
  exact_mod_cast hp

private theorem prod_value_int (n : ℕ) (hn : 0 < n) :
    (∏ d ∈ n.divisors, (cycloValue d : ℤ)) = 2^n-1 := by
  simpa only [cast_cycloValue, eval_prod, eval_sub, eval_pow, eval_X, eval_one] using
    congrArg (eval (2 : ℤ)) (prod_cyclotomic_eq_X_pow_sub_one hn ℤ)

theorem odd_cyclo_product {N : ℕ} (hN : Odd N) :
    ∏ d ∈ N.divisors, cycloValue (2*d) = 2^N+1 := by
  have hn : 0<N := by obtain ⟨k,h⟩ := hN; omega
  have h := prod_value_int (2*N) (by omega)
  rw [hN.coprime_two_left.divisors_mul, prod_map] at h
  change (∏ t ∈ ((2:ℕ).divisors ×ˢ N.divisors).attach,
    (cycloValue (t.val.1*t.val.2) : ℤ)) = _ at h
  rw [prod_attach _ (fun t : ℕ × ℕ => (cycloValue (t.1*t.2):ℤ)), prod_product] at h
  rw [show (2 : ℕ).divisors = {1,2} by decide] at h
  rw [prod_insert (by decide : (1:ℕ) ∉ ({2} : Finset ℕ)), prod_singleton] at h
  simp only [one_mul, prod_value_int N hn] at h
  have hpow : (1 : ℤ) < 2^N := one_lt_pow₀ (by norm_num) hn.ne'
  rw [two_mul, pow_add] at h
  have hdiv : (∏ d ∈ N.divisors, (cycloValue (2*d) : ℤ)) = 2^N+1 := by
    apply mul_left_cancel₀ (sub_ne_zero.mpr hpow.ne') (b := _)
    rw [h]
    ring
  exact_mod_cast hdiv

private def normalized (n : ℕ) : ℚ := (cycloValue n : ℚ) / 2^n.totient
private def correction (n : ℕ) : ℚ := 1-(1/2:ℚ)^n

private theorem correction_pos {n : ℕ} (hn : 0<n) : 0<correction n := by
  simpa [correction] using pow_lt_one₀ (show (0:ℚ) ≤ 1/2 by norm_num)
    (show (1/2:ℚ)<1 by norm_num) hn.ne'

private theorem correction_le_one (n : ℕ) : correction n ≤ 1 := by
  unfold correction
  have hp : (0:ℚ) ≤ (1/2:ℚ)^n := by positivity
  linarith

private theorem normalized_divisors (n : ℕ) (hn : 0<n) :
    ∏ d ∈ n.divisors, normalized d = correction n := by
  have hi := prod_value_int n hn
  have hq : (∏ d ∈ n.divisors, (cycloValue d : ℚ)) = 2^n-1 := by exact_mod_cast hi
  simp only [normalized, prod_div_distrib, prod_pow_eq_pow_sum, Nat.sum_totient, hq, correction]
  rw [div_pow, one_pow]
  field_simp

private theorem correction_moebius (n : ℕ) (hn : 0<n) :
    (∏ d ∈ n.divisors, correction d ^ (ArithmeticFunction.moebius (n/d))) =
      normalized n := by
  have hh := (ArithmeticFunction.prod_eq_iff_prod_pow_moebius_eq_of_nonzero
    (f := normalized) (g := correction) (fun j _ => div_ne_zero
      (by exact_mod_cast (cycloValue_pos j).ne') (by positivity))
    (fun _ hj => (correction_pos hj).ne')).mp normalized_divisors n hn
  exact (Nat.prod_divisorsAntidiagonal' (fun i j => correction j ^
    (ArithmeticFunction.moebius i))).symm.trans hh

private theorem correction_range (n : ℕ) :
    1/4+(1/2:ℚ)^(n+2) ≤ ∏ d ∈ Icc 1 (n+1), correction d := by
  induction n with
  | zero => norm_num [correction]
  | succ n ih =>
    rw [Finset.prod_Icc_succ_top (by omega : 1 ≤ n+1+1)]
    have ht : (1/2:ℚ)^(n+2) ≤ 1/4 := by
      rw [pow_add]
      have hone : (1/2:ℚ)^n ≤ 1 := pow_le_one₀ (show (0:ℚ)≤1/2 by norm_num)
        (show (1/2:ℚ)≤1 by norm_num)
      norm_num
      linarith
    have hp : (0:ℚ) ≤ (1/2:ℚ)^(n+2) := by positivity
    have hh := mul_le_mul_of_nonneg_right ih (correction_pos (n := n+2) (by omega)).le
    calc
      _ ≤ (1/4+(1/2:ℚ)^(n+2))*correction (n+2) := by
        change 1/4+(1/2:ℚ)^((n+2)+1) ≤ _
        rw [pow_succ]
        unfold correction
        nlinarith [mul_nonneg hp (sub_nonneg.mpr ht)]
      _ ≤ _ := hh

private theorem correction_prod_lower (n : ℕ) (hn : 0<n) :
    (1/4:ℚ) ≤ ∏ d ∈ n.divisors, correction d := by
  obtain ⟨k,rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  have sub : (k+1).divisors ⊆ Icc 1 (k+1) := by
    intro d hd
    exact mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd, Nat.divisor_le hd⟩
  have hle := prod_le_prod_of_subset_of_le_one (f := correction) sub
    (fun i hi => (correction_pos (mem_Icc.mp hi).1).le)
    (fun i _ _ => correction_le_one i)
  have h := correction_range k
  have : 0 ≤ (1/2:ℚ)^(k+2) := by positivity
  linarith

theorem cycloValue_bounds (n : ℕ) (hn : 0<n) :
    2^n.totient ≤ 4*cycloValue n ∧ cycloValue n ≤ 4*2^n.totient := by
  have point (d : ℕ) (hd : d ∈ n.divisors) :
      correction d ≤ correction d ^ (ArithmeticFunction.moebius (n/d)) ∧
      correction d ^ (ArithmeticFunction.moebius (n/d)) ≤ (correction d)⁻¹ := by
    have ha := correction_pos (Nat.pos_of_mem_divisors hd)
    have hb := correction_le_one d
    have hc : 1 ≤ (correction d)⁻¹ := (one_le_inv₀ ha).mpr hb
    rcases ArithmeticFunction.moebius_eq_or (n/d) with h | h | h <;>
      simp only [h, zpow_zero, zpow_one, zpow_neg_one] <;>
      exact ⟨by first | exact hb | exact le_rfl | exact hb.trans hc,
             by first | exact hc | exact le_rfl | exact hb.trans hc⟩
  have hl := Finset.prod_le_prod (fun d hd => (correction_pos (Nat.pos_of_mem_divisors hd)).le)
    (fun d hd => (point d hd).1)
  have hu := Finset.prod_le_prod (fun d hd =>
    (correction_pos (Nat.pos_of_mem_divisors hd)).le.trans (point d hd).1)
    (fun d hd => (point d hd).2)
  rw [correction_moebius n hn] at hl hu
  rw [prod_inv_distrib] at hu
  have lower := correction_prod_lower n hn
  have hi : (∏ d ∈ n.divisors, correction d)⁻¹ ≤ 4 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    norm_num
    exact lower
  have h1 := lower.trans hl
  have h2 := hu.trans hi
  unfold normalized at h1 h2
  rw [le_div_iff₀ (by positivity)] at h1
  rw [div_le_iff₀ (by positivity)] at h2
  constructor
  · have : (2:ℚ)^n.totient ≤ 4*(cycloValue n : ℚ) := by linarith
    exact_mod_cast this
  · exact_mod_cast h2


end
end PracticalTriples
end

section
namespace PracticalTriples

open PracticalComplements

/-- Adjoining a bounded new odd prime power preserves the two induction
hypotheses on the divisor order and the associated practical number. -/
theorem extend_prime_power {N p : ℕ} (hN : Odd N) (hO : Ordered N)
    (hQ : practical (2*(2^N+1))) (hp : p.Prime) (hp2 : p ≠ 2) (hnew : ¬ p ∣ N)
    (hsize : 6*(p-1) ≤ N) (e : ℕ) :
    Ordered (N*p^e) ∧ practical (2*(2^(N*p^e)+1)) :=
  extend_for_property cycloValue_bounds (@odd_cyclo_product) (@mul_double)
    hN hO hQ hp hp2 hnew hsize e

end PracticalTriples
end

section
namespace PracticalTriples

/-- An ordered prime-power factorization above a fixed initial divisor. -/
inductive Profile (B : ℕ) : ℕ → Prop where
  | seed : Profile B B
  | extend {n p : ℕ} : Profile B n → p.Prime → p ≠ 2 → ¬p ∣ n →
      6*(p-1) ≤ n → (e : ℕ) → Profile B (n*p^(e+1))

theorem Profile.base_dvd {B n : ℕ} (h : Profile B n) : B ∣ n := by
  induction h with
  | seed => exact dvd_rfl
  | extend _ _ _ _ _ _ ih => exact dvd_mul_of_dvd_left ih _

/-- Increase the exponent of a prime which is already present above the base. -/
theorem Profile.bump {B n p : ℕ} (h : Profile B n) (hp : p.Prime) (hb : ¬ p ∣ B)
    (hd : p ∣ n) : Profile B (n*p) := by
  revert hd
  induction h with
  | seed => exact fun hd => False.elim (hb hd)
  | @extend n r h hr hr2 hnew hsize e ih =>
    intro hd
    by_cases he : p=r
    · subst p
      simpa only [pow_succ r (e+1), Nat.mul_assoc] using h.extend hr hr2 hnew hsize (e+1)
    · have hpn : p ∣ n := (hp.dvd_mul.mp hd).resolve_right (fun hpow =>
        he ((Nat.prime_dvd_prime_iff_eq hp hr).mp (hp.dvd_of_dvd_pow hpow)))
      have hrnew : ¬ r ∣ n*p := fun hdiv => (hr.dvd_mul.mp hdiv).elim hnew
        (fun hdivp => he ((Nat.prime_dvd_prime_iff_eq hr hp).mp hdivp).symm)
      have hle : n ≤ n*p := by nlinarith [hp.one_lt]
      have hg := (ih hpn).extend hr hr2 hrnew (hsize.trans hle) e
      simpa only [Nat.mul_right_comm n p (r^(e+1))] using hg

theorem Profile.add_prime {B n p : ℕ} (h : Profile B n) (hp : p.Prime) (hodd : p ≠ 2)
    (hb : ¬ p ∣ B) (hle : 6*(p-1) ≤ n) : Profile B (n*p) := by
  by_cases hd : p∣n
  · exact h.bump hp hb hd
  · simpa using h.extend hp hodd hd hle 0

theorem Profile.add_factor {B n t : ℕ} (h : Profile B n) (ht : Odd t) (hcop : t.Coprime B)
    (hle : 6*(t-1) ≤ n) : Profile B (n*t) := by
  induction t using Nat.strong_induction_on generalizing n with
  | h t ih =>
    have ht0 : 0<t := by rcases ht with ⟨u,hu⟩; omega
    by_cases hone : t=1
    · simpa [hone] using h
    · let p := t.minFac
      have hp : p.Prime := Nat.minFac_prime hone
      have hpt : p∣t := Nat.minFac_dvd t
      obtain ⟨v,hv⟩ := hpt
      have hv0 : 0<v := by by_contra! hz; simp_all
      have hvlt : v<t := by nlinarith [hp.one_lt]
      have hpd : p∣t := ⟨v,hv⟩
      have hvd : v∣t := ⟨p,hv.trans (Nat.mul_comm p v)⟩
      have hpc := Nat.Coprime.coprime_dvd_left hpd hcop
      have hvc := Nat.Coprime.coprime_dvd_left hvd hcop
      have hpo : p≠2 := by
        intro he
        rw [he] at hv
        rcases ht with ⟨j,hj⟩
        omega
      have hvodd : Odd v := by
        rw [hv, Nat.odd_mul] at ht
        exact ht.2
      have hplt := Nat.le_of_dvd ht0 hpd
      have hpB : ¬p∣B := hp.coprime_iff_not_dvd.mp hpc
      have hg := h.add_prime hp hpo hpB (by omega)
      have hnle : n ≤ n*p := by nlinarith [hp.one_lt]
      have hmore := ih v hvlt hg hvodd hvc (by omega)
      simpa only [hv, Nat.mul_assoc] using hmore

end PracticalTriples
end

section
namespace PracticalTriples

open PracticalComplements

theorem profile_sound {C k : ℕ} (hC : Odd C) (hO : Ordered C)
    (hQ : practical (2*(2^C+1))) (h : Profile C k) :
    Odd k ∧ Ordered k ∧ practical (2*(2^k+1)) := by
  induction h with
  | seed => exact ⟨hC, hO, hQ⟩
  | extend _ hp h2 hnew hsize e ih =>
    exact ⟨ih.1.mul ((hp.odd_of_ne_two h2).pow),
      extend_prime_power ih.1 ih.2.1 ih.2.2 hp h2 hnew hsize (e+1)⟩

end PracticalTriples
end

section
namespace PracticalTriples.SeedRows
open Finset
open scoped Pointwise

abbrev Row := ℕ × ℕ
abbrev keys (xs : List Row) := xs.map Prod.fst

structure Correct (n : ℕ) (xs : List Row) : Prop where
  nodup : (keys xs).Nodup
  mem : ∀ d, d ∈ keys xs ↔ d ∈ n.divisors
  weight : ∀ r ∈ xs, r.2 = r.1.totient

def extend (p : ℕ) (xs : List Row) : List Row :=
  xs ++ xs.map (fun r => (r.1*p,r.2*(p-1)))

theorem correct_extend {n p : ℕ} {xs : List Row} (h : Correct n xs)
    (hp : p.Prime) (hc : n.Coprime p) : Correct (n*p) (extend p xs) := by
  have hk : keys (extend p xs) = keys xs ++ (keys xs).map (·*p) := by
    simp [keys, extend, List.map_map, Function.comp_def]
  have hem (d : ℕ) : d ∈ keys (extend p xs) ↔
      d ∈ n.divisors ∨ ∃ a ∈ n.divisors, a*p=d := by
    rw [hk]
    simp only [List.mem_append, List.mem_map, h.mem]
  constructor
  · rw [hk]
    refine h.nodup.append (h.nodup.map (fun _ _ hxy => Nat.eq_of_mul_eq_mul_right hp.pos hxy)) ?_
    intro t ht ht'
    obtain ⟨a,_,rfl⟩ := List.mem_map.mp ht'
    exact (hp.coprime_iff_not_dvd.mp hc.symm)
      ((dvd_mul_left p a).trans (Nat.dvd_of_mem_divisors ((h.mem _).mp ht)))
  · intro d
    rw [hem, Nat.divisors_mul, Finset.mem_mul, hp.divisors]
    constructor
    · rintro (hd|⟨a,ha,rfl⟩)
      · exact ⟨d,hd,1,by simp,by simp⟩
      · exact ⟨a,ha,p,by simp,rfl⟩
    · rintro ⟨a,ha,b,hb,rfl⟩
      simp only [mem_insert,mem_singleton] at hb
      rcases hb with rfl|rfl
      · simpa using Or.inl (b := ∃ x ∈ n.divisors, x*p=a) ha
      · exact Or.inr ⟨a,ha,rfl⟩
  · intro r hr
    rcases List.mem_append.mp hr with hr|hr
    · exact h.weight r hr
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      have hd : s.1 ∈ n.divisors := (h.mem _).mp (List.mem_map.mpr ⟨s,hs,rfl⟩)
      rw [Prod.fst, Prod.snd, Nat.totient_mul (hc.coprime_dvd_left (Nat.dvd_of_mem_divisors hd)),
        h.weight s hs, Nat.totient_prime hp]

/-- Merge the two lists according to the supplied low-order selector bits.
Every possible selector represents a permutation of the concatenation. -/
def interleave : ℕ → ℕ → List Row → List Row → List Row
  | 0,_,xs,ys => xs++ys
  | _+1,_,[],ys => ys
  | _+1,_,xs,[] => xs
  | k+1,m,x::xs,y::ys =>
    if m%2=0 then x::interleave k (m/2) xs (y::ys)
    else y::interleave k (m/2) (x::xs) ys

private theorem interleave_perm (k m : ℕ) (xs ys : List Row) :
    (interleave k m xs ys).Perm (xs++ys) := by
  induction k generalizing m xs ys with
  | zero => rfl
  | succ k ih =>
    cases xs with
    | nil => rfl
    | cons x xs =>
      cases ys with
      | nil => simp [interleave]
      | cons y ys =>
        simp only [interleave]
        split
        · exact (ih _ _ _).cons x
        · exact List.perm_cons_append_cons y (ih _ _ _)

def routed (p mask : ℕ) (xs : List Row) : List Row :=
  interleave (2*xs.length) mask xs (xs.map (fun r => (r.1*p,r.2*(p-1))))

theorem correct_routed {n p : ℕ} {xs : List Row} (mask : ℕ) (h : Correct n xs)
    (hp : p.Prime) (hc : n.Coprime p) : Correct (n*p) (routed p mask xs) := by
  have hh := correct_extend h hp hc
  have he : (routed p mask xs).Perm (extend p xs) := interleave_perm _ _ _ _
  have hk := he.map Prod.fst
  exact ⟨hk.nodup_iff.mpr hh.nodup,fun d => hk.mem_iff.trans (hh.mem d),
    fun r hr => hh.weight r (he.mem_iff.mp hr)⟩

def build : List (ℕ × ℕ) → List Row → List Row
  | [],xs => xs
  | (p,m)::ps,xs => build ps (routed p m xs)

def finalIndex : List (ℕ × ℕ) → ℕ → ℕ
  | [],n => n
  | (p,_)::ps,n => finalIndex ps (n*p)

def validPrimes : List (ℕ × ℕ) → ℕ → Bool
  | [],_ => true
  | (p,_)::ps,n => decide p.Prime && decide (n.Coprime p) && validPrimes ps (n*p)

theorem correct_build (ps : List (ℕ × ℕ)) {n : ℕ} {xs : List Row}
    (hn : Correct n xs) (hv : validPrimes ps n = true) :
    Correct (finalIndex ps n) (build ps xs) := by
  induction ps generalizing n xs with
  | nil => exact hn
  | cons pm ps ih =>
    obtain ⟨p,m⟩ := pm
    simp only [validPrimes,Bool.and_eq_true,decide_eq_true_eq] at hv
    exact ih (correct_routed m hn hv.1.1 hv.1.2) hv.2

def recipeA : List (ℕ × ℕ) := [
  (13,0x8),
  (19,0x690),
  (29,0x1bd1280),
  (31,0xefb6555b108900),
  (43,0x3dfebce5b9beac2e0962d304104400),
  (53,0x1f7fdf79ed5bed7b7e5795e252d54aeb5a47c8b04c8812a495218200810800),
  (59,0x7efff7bf3fcdb5ff3bdbbf3ddeadf7133cd3ae785adb5bbc763bb236ec658de428cc91164f0c68a65d266592267020b208628012498489441804010082000),
  (67,0x3fbfffbeff3fdbb7d5febfb7faefcfb7fd67ff629ebe9ef3b177f14edbcadf739b7bf873bbf28bafee16e63fe38a37b6c8c47f8922976d341dec5911f65326db2e643dbcb6063ee3c00ef166301d636818a63d0022d3840a58229af00a5c8452d8268b33041b41019c04063100860240150122a8090510180200100208000),
  (79,0x1ffbfffefbfe7ffd7defcbeffd7dfbfdaffb5febfedef7ffd927f9dbf37bf3c77c6ffdc57bcceebd6fe766fde66ffbc75f7e6b6a7badff6e47bdbb4e7d7daab657f9ae9b5d86cf7d8e1cbd1f2617bcbc8cdf736536e34d0edfa70f2db7c62acd76879badf527f58da671bb7b3624e4bdf22d58d9a896b54bd8e664eb5d124637d0e812ae96ab921d462509a3d8a0c971d229587ce0347279893aa54289adaa9129f3a16c30dcc6284a7a4e515b580cc59b07081394b16103c4500b1a894548702250e90006320565300491221ac182ba900ac145160a4988855a013c30044642820196004100a940020500a0040582048b202020c10060008001000820000)]
def rowsA : List Row := build recipeA [(1,1),(3,2),(9,6),(27,18)]

def recipeB : List (ℕ × ℕ) := [
  (5,0x0),
  (7,0x0),
  (11,0x8),
  (17,0x710),
  (23,0x3d55420),
  (37,0xfd769e86914080),
  (41,0x7fb7b76d739b34d326314912120100),
  (47,0x1fef7bdf9f1f3f3e8fc3f0fa3e83e0f83e83a0f03c0e830307060421080400),
  (61,0xfff7befef7bed5fafb7f6cf679ddb3bcf5db2a7b555ad5af5a396b93365869e593362963a50a54a55521ab2450c232446190c90120a054821080821000800),
  (71,0x1fff7dfbff7edff737f97fb7fdef2ff5c77fc6befbdb9def6786ff363cf3f8ee3b8fbb8e1ddf8f8b9e79d17e171f99c8ea5cfc3c4e74f8e39e0789e477128eb711d86e1f8638e0d18dc3c0c5a8ec660717817461862e0e04478e220e2388e030c393009e1908462420829c011c500b0840120160131004810020410004000),
  (73,0xfffdfbfbffbfbbffbceffcd7fbbff7ef9eff9f8f3ffd3adefdfd7cdfb7f8fe2f3fe7f87acfcffb3ee3cf87dbbf47e34f9bfc7fc5d67f9e7fa1fb8e3f07fb8fee0f4f41eaefe2fe33a3d1f9f17fc3771e0fe0f3ee0fee1c4f80ed73ff03f1b607b875fc47f8a761f407c3c4ff06ee3847c0e6dc3f78791ba03b86bfc41fc55c07dc029e23fa2761e103c498fc1de3889f00dc3c1fd0791ae01dc051e21f92703f003148fe0dc7880f8830f80f87113c017060743a3380b808a87d0d0f880e201f038e207a018601945c01c0260d381d02241e0c3883200c0ca1e018030b80e01204c1404084a340030e0600860810022014c008c200220200202040008000)]
def rowsB : List Row := build recipeB [(1,1)]

theorem rowsA_correct : Correct 4266960671228463 rowsA := by
  apply correct_build recipeA (n := 27)
    (xs := [(1,1),(3,2),(9,6),(27,18)])
  · constructor
    · decide
    · intro d
      rw [show (27:ℕ).divisors={1,3,9,27} by decide]
      simp [keys]
    · rintro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl|rfl|rfl|rfl <;> decide
  · decide

theorem rowsB_correct : Correct 3393375887119295 rowsB := by
  apply correct_build recipeB (n := 1) (xs := [(1,1)])
  · constructor
    · decide
    · simp [keys]
    · rintro r hr
      simp only [List.mem_singleton] at hr
      subst r
      decide
  · decide

end PracticalTriples.SeedRows
end

section
namespace PracticalTriples.SeedRows

def degreeCheck : ℕ → List Row → Bool
  | _,[] => true
  | s,r::rs => decide (r.2 ≤ s+3) && degreeCheck (s+r.2) rs

def growthCheck : ℕ → List Row → Bool
  | _,[] => true
  | L,r::rs => decide (2 ≤ r.2 ∧ r.2+2 ≤ L+1) && growthCheck (L+(r.2-2)) rs

def firstRows (star : List ℕ) (xs : List Row) := xs.filter (fun r => star.contains r.1)
def otherRows (star : List ℕ) (xs : List Row) := xs.filter (fun r => !(star.contains r.1))

def seedCheck (xs : List Row) (star : List ℕ) (L : ℕ) : Bool :=
  decide (xs.length = 2048) && degreeCheck 0 xs &&
    decide (keys (firstRows star xs) = star) && growthCheck L (otherRows star xs)

def starA : List ℕ := [1,3,9,13,27]
def starB : List ℕ := [1,5,7,11,17]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem seed_numbers_A : seedCheck rowsA starA 39 = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 3000000 in
theorem seed_numbers_B : seedCheck rowsB starB 36 = true := by decide +kernel

end PracticalTriples.SeedRows
end

section
namespace PracticalTriples
open Finset

theorem cycloValue_two : cycloValue 2 = 3 := by
  simpa using odd_cyclo_product (N := 1) (by decide)

private theorem value_prime_eq {p : ℕ} (hp : p.Prime) (ho : Odd p) :
    3*cycloValue (2*p) = 2^p+1 := by
  have h := odd_cyclo_product ho
  rw [hp.divisors, Finset.prod_insert, Finset.prod_singleton] at h
  · simpa [cycloValue_two, Nat.mul_comm] using h
  · simpa using hp.ne_one.symm

theorem starter_values :
    cycloValue 2 = 3 ∧ cycloValue 6 = 3 ∧ cycloValue 18 = 57 ∧
    cycloValue 26 = 2731 ∧ cycloValue 54 = 261633 ∧
    cycloValue 10 = 11 ∧ cycloValue 14 = 43 ∧ cycloValue 22 = 683 ∧
    cycloValue 34 = 43691 := by
  have h3 := value_prime_eq (p := 3) (by decide) (by decide)
  have h5 := value_prime_eq (p := 5) (by decide) (by decide)
  have h7 := value_prime_eq (p := 7) (by decide) (by decide)
  have h11 := value_prime_eq (p := 11) (by decide) (by decide)
  have h13 := value_prime_eq (p := 13) (by decide) (by decide)
  have h17 := value_prime_eq (p := 17) (by decide) (by decide)
  norm_num at h3 h5 h7 h11 h13 h17
  have h6 : cycloValue 6=3 := by omega
  have h9 := odd_cyclo_product (N := 9) (by decide)
  rw [show Nat.divisors 9={1,3,9} by decide] at h9
  norm_num [Finset.prod_insert, cycloValue_two, h6] at h9
  have h18 : cycloValue 18=57 := by omega
  have h27 := odd_cyclo_product (N := 27) (by decide)
  rw [show Nat.divisors 27={1,3,9,27} by decide] at h27
  norm_num [Finset.prod_insert, cycloValue_two, h6, h18] at h27
  refine ⟨cycloValue_two,h6,h18,?_,?_,?_,?_,?_,?_⟩ <;> omega

end PracticalTriples
end

section
namespace PracticalTriples
open PracticalComplements SeedRows

private theorem checkedGap {s : ℕ} {xs : List Row} (hh : degreeCheck s xs = true)
    (hw : ∀ r ∈ xs, r.2 = r.1.totient) : Gap Nat.totient s (keys xs) := by
  induction xs generalizing s with
  | nil => trivial
  | cons r xs ih =>
    have eq := hw r (by simp)
    simp only [degreeCheck,Bool.and_eq_true,decide_eq_true_eq] at hh
    change r.1.totient ≤ s+3 ∧ Gap Nat.totient (s+r.1.totient) (keys xs)
    rw [← eq]
    exact ⟨hh.1,ih hh.2 (fun t ht => hw t (by simp [ht]))⟩

private noncomputable def productRows (xs : List Row) : ℕ :=
  (xs.map (fun r => cycloValue (2*r.1))).prod

private theorem split_product (star : List ℕ) (xs : List Row) :
    productRows (firstRows star xs) * productRows (otherRows star xs) =
      productRows xs := by
  have hh := (List.filter_append_perm (fun r : Row => star.contains r.1) xs).map
    (fun r => cycloValue (2*r.1))
  simpa only [productRows,firstRows,otherRows,List.map_append,List.prod_append] using hh.prod_eq

private theorem product_rows_value {N : ℕ} {xs : List Row} (h : Correct N xs) (hN : Odd N) :
    productRows xs = 2^N+1 := by
  have he : (keys xs).toFinset = N.divisors := by
    ext d
    exact List.mem_toFinset.trans (h.mem d)
  rw [← odd_cyclo_product hN, ← he, List.prod_toFinset _ h.nodup]
  simp [productRows,keys,List.map_map,Function.comp_def]

private theorem checkedGrowth {N L M : ℕ} {rs : List Row} (hN : Odd N)
    (hrow : ∀ r ∈ rs, r.1 ∈ N.divisors ∧ r.2 = r.1.totient)
    (h : growthCheck L rs = true) (hp : practical M) (hl : 2^L ≤ M) :
    practical (M * productRows rs) := by
  induction rs generalizing M L with
  | nil => simpa [productRows] using hp
  | cons r rs ih =>
    have hz := hrow r (by simp)
    have hd0 := Nat.pos_of_mem_divisors hz.1
    have hodd : Odd r.1 := (hN.coprime_two_left.coprime_dvd_right
      (Nat.dvd_of_mem_divisors hz.1)).odd_of_left
    have hh := cycloValue_bounds (2*r.1) (by omega)
    rw [Nat.totient_two_mul_of_odd hodd, ← hz.2] at hh
    simp only [growthCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    have hpow : 4*(2:ℕ)^r.2 ≤ 2*2^L := by
      calc
        4*(2:ℕ)^r.2 = 2^(r.2+2) := by rw [pow_add]; ring
        _ ≤ 2^(L+1) := Nat.pow_le_pow_right (by decide) h.1.2
        _ = 2*2^L := by rw [pow_succ,Nat.mul_comm]
    have key : 2^(r.2-2) ≤ cycloValue (2*r.1) := by
      have e : r.2 = r.2-2+2 := by omega
      have lo := hh.1
      conv at lo => lhs; rw [e,pow_add]
      norm_num only [Nat.reducePow] at lo
      omega
    have nextL : 2^(L+(r.2-2)) ≤ M*cycloValue (2*r.1) := by
      rw [pow_add]
      exact Nat.mul_le_mul hl key
    have hm0 : 0<M := (pow_pos (by decide : 0<2) _).trans_le hl
    have next := ih (fun s hs => hrow s (by simp [hs])) h.2
      (mul_double hp hm0 (cycloValue_pos _) (hh.2.trans (hpow.trans (Nat.mul_le_mul_left 2 hl))))
      nextL
    simpa only [productRows,List.map_cons,List.prod_cons,Nat.mul_assoc] using next

private def doubleCheck : ℕ → List ℕ → Bool
  | _,[] => true
  | M,v::vs => decide (0<v ∧ v≤2*M) && doubleCheck (M*v) vs

private theorem smallProduct (vs : List ℕ) {m : ℕ} (hm : practical m) (hm0 : 0 < m)
    (h : doubleCheck m vs=true) : practical (m*vs.prod) := by
  induction vs generalizing m with
  | nil => simpa using hm
  | cons v vs ih =>
    simp only [doubleCheck,Bool.and_eq_true,decide_eq_true_eq] at h
    have step := ih (mul_double hm hm0 h.1.1 h.1.2) (Nat.mul_pos hm0 h.1.1) h.2
    simpa only [List.prod_cons,Nat.mul_assoc] using step

private theorem verified_seed {N L : ℕ} (hN : Odd N) {xs : List Row} {star : List ℕ}
    (h : Correct N xs) (hb : seedCheck xs star L=true) (hbig : 4*2048≤N)
    (hp : practical (2*(star.map (fun d => cycloValue (2*d))).prod))
    (hl : 2^L ≤ 2*(star.map (fun d => cycloValue (2*d))).prod) :
    Ordered N ∧ practical (2*(2^N+1)) := by
  simp only [seedCheck,Bool.and_eq_true,decide_eq_true_eq] at hb
  have he : (keys xs).toFinset = N.divisors := by
    ext d
    exact List.mem_toFinset.trans (h.mem d)
  refine ⟨⟨keys xs,h.nodup,he,by simpa only [keys,List.length_map,hb.1.1.1] using hbig,
    checkedGap hb.1.1.2 h.weight⟩,?_⟩
  have hstarter : productRows (firstRows star xs) = (star.map (fun d => cycloValue (2*d))).prod := by
    calc
      _ = ((keys (firstRows star xs)).map (fun d => cycloValue (2*d))).prod := by
        simp [productRows,keys,List.map_map,Function.comp_def]
      _ = _ := congrArg (fun ds : List ℕ => (ds.map (fun d => cycloValue (2*d))).prod) hb.1.2
  rw [← hstarter] at hp hl
  have ht : ∀ r ∈ otherRows star xs, r.1 ∈ N.divisors ∧ r.2=r.1.totient := by
    intro r hr
    have hh := (List.mem_filter.mp hr).1
    exact ⟨(h.mem _).mp (List.mem_map.mpr ⟨r,hh,rfl⟩),h.weight r hh⟩
  have := checkedGrowth hN ht hb.2 hp hl
  rwa [Nat.mul_assoc,split_product,product_rows_value h hN] at this

private theorem starter_A :
    2*(starA.map (fun d => cycloValue (2*d))).prod = 733097235798 := by
  obtain ⟨a,b,c,d,e,-,-,-,-⟩ := starter_values
  norm_num [starA,a,b,c,d,e]

private theorem starter_B :
    2*(starB.map (fun d => cycloValue (2*d))).prod = 84688624614 := by
  obtain ⟨a,-,-,-,-,b,c,d,e⟩ := starter_values
  norm_num [starB,a,b,c,d,e]

theorem seed_A_verified : Ordered 4266960671228463 ∧
    practical (2*(2^4266960671228463+1)) := by
  apply verified_seed (by decide) rowsA_correct seed_numbers_A (by decide)
  · rw [starter_A]
    exact smallProduct [2,3,3,3,3,19,2731,87211] practical_one (by decide) (by decide)
  · rw [starter_A]
    decide

theorem seed_B_verified : Ordered 3393375887119295 ∧
    practical (2*(2^3393375887119295+1)) := by
  apply verified_seed (by decide) rowsB_correct seed_numbers_B (by decide)
  · rw [starter_B]
    exact smallProduct [2,3,11,43,683,43691] practical_one (by decide) (by decide)
  · rw [starter_B]
    decide

end PracticalTriples
end

section
namespace PracticalTriples

def baseA : ℕ := 4266960671228463
def baseB : ℕ := 3393375887119295
def startM : ℕ := 4711948260850737087319607727600438057

structure Coupled (m : ℕ) : Prop where
  left : Profile baseA m
  right : Profile baseB (2*m+1)
  dleft : 103 ∣ m
  dright : 101 ∣ 2*m+1
  pos : 0 < m

theorem initial : Coupled startM := by
  have a₀ : Profile baseA baseA := .seed
  have a₁ := a₀.add_factor (t:=103) (by decide) (by decide) (by decide)
  have a₂ := a₁.add_factor (t:=397) (by decide) (by decide) (by decide)
  have a₃ := a₂.add_factor (t:=27005619334212229) (by decide) (by decide) (by decide)
  have b₀ : Profile baseB baseB := .seed
  have b₁ := b₀.add_factor (t:=101) (by decide) (by decide) (by decide)
  have b₂ := b₁.add_factor (t:=163) (by decide) (by decide) (by decide)
  have b₃ := b₂.add_factor (t:=168690086557234819) (by decide) (by decide) (by decide)
  exact ⟨a₃,b₃,by decide,by decide,by decide⟩

def nextM (m : ℕ) := m*(1+102*(2*m+1))

theorem lt_next {m : ℕ} (hm : 0 < m) : m < nextM m := by
  unfold nextM
  nlinarith

theorem advance {m : ℕ} (h : Coupled m) : Coupled (nextM m) := by
  let n := 2*m+1
  have hr : Profile baseB n := h.right
  have hdn : 101∣n := h.dright
  obtain ⟨a,ha⟩:=h.left.base_dvd
  obtain ⟨b,hb⟩:=hr.base_dvd
  obtain ⟨j,hj⟩:=h.dleft
  obtain ⟨k,hk⟩:=hdn
  have heq : 2*nextM m+1=n*(1+204*m) := by dsimp [nextM,n]; ring
  have hma : 1+102*n = 103+baseA*(204*a) := by dsimp [n]; rw [ha]; ring
  have cA : (1+102*n).Coprime baseA := by
    rw [hma,Nat.coprime_add_mul_left_left]
    decide
  have hdb : 101+ (1+204*m) = 102*n := by dsimp [n]; omega
  have cB : (1+204*m).Coprime baseB := by
    by_contra hn
    obtain ⟨p,hp,hd₁,hd₂⟩ := Nat.Prime.not_coprime_iff_dvd.mp hn
    have hpn : p∣n := hd₂.trans hr.base_dvd
    have hs : p∣101+(1+204*m) := hdb ▸ dvd_mul_of_dvd_right hpn _
    have hd₃ : p∣101 := (Nat.dvd_add_iff_left hd₁).mpr hs
    have hfalse : (101:ℕ).Coprime baseB := by decide
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨p,hp,hd₃,hd₂⟩) hfalse
  have left_old := h.left.bump (p:=103) (by norm_num) (by decide) h.dleft
  have right_old := hr.bump (p:=101) (by norm_num) (by decide) h.dright
  let x:=204*j+1
  let y:=102*k-1
  have ex : 1+102*n=103*x := by dsimp [x,n]; rw [hj]; ring
  have kn : 0<k := by dsimp [n] at hk; omega
  have ey : 1+204*m=101*y := by dsimp [y,n] at *; omega
  have cx : x.Coprime baseA := Nat.Coprime.coprime_dvd_left
    (ex.symm ▸ dvd_mul_left x 103) cA
  have cy : y.Coprime baseB := Nat.Coprime.coprime_dvd_left
    (ey.symm ▸ dvd_mul_left y 101) cB
  have oy : Odd y := by
    use 51*k-1
    dsimp [y]
    omega
  have ox : Odd x := ⟨102*j,by dsimp [x]; omega⟩
  have xl : 6*(x-1) ≤ m*103 := by dsimp [x]; omega
  have yl : 6*(y-1) ≤ n*101 := by dsimp [y]; omega
  have nx : nextM m=m*103*x := by
    change m*(1+102*n)=_
    rw [ex,Nat.mul_assoc]
  have ny : 2*nextM m+1=n*101*y := by rw [heq,ey,Nat.mul_assoc]
  refine ⟨nx ▸ left_old.add_factor ox cx xl, ny ▸ right_old.add_factor oy cy yl, ?_, ?_, ?_⟩
  · exact dvd_mul_of_dvd_left h.dleft _
  · rw [heq]
    exact dvd_mul_of_dvd_left h.dright _
  · exact h.pos.trans (lt_next h.pos)

end PracticalTriples
end

section
namespace PracticalTriples

open PracticalComplements

theorem practical_two_pow (e : ℕ) : practical (2^e) := by
  induction e with
  | zero => simpa using practical_one
  | succ e ih =>
    have hpos : 0<(2:ℕ)^e := by positivity
    simpa only [pow_succ] using mul_double ih hpos (by decide : 0<2) (by omega)

theorem source_practical {n : ℕ} (hn : 0<n) (hp : practical n) :
    OMA.S_oeis_a294225.IsPractical n := by
  refine ⟨hn,?_⟩
  intro t ht
  obtain ⟨s,hs,he⟩ := hp t ht
  exact ⟨s,hs,he.symm⟩

theorem large_coupled (x : ℕ) : ∃ m : ℕ, Coupled m ∧ x ≤ m := by
  induction x with
  | zero => exact ⟨_, initial, Nat.zero_le _⟩
  | succ x ih =>
    obtain ⟨m,hm,hx⟩ := ih
    exact ⟨nextM m,advance hm,hx.trans_lt (lt_next hm.pos)⟩

theorem solution_of_profiles
    (ha : ∀ m, Profile baseA m → practical (2*(2^m+1)))
    (hb : ∀ n, Profile baseB n → practical (2*(2^n+1))) :
    type_of% @OMA.S_oeis_a294225.main := by
  apply Set.infinite_of_forall_exists_gt
  intro x
  obtain ⟨m,hm,hx⟩ := large_coupled x
  have first : practical (2^(m+1)+2) := by
    convert ha m hm.left using 1 <;> rw [pow_succ] <;> ring
  have second : practical ((2^(m+1))^2+2) := by
    rw [← pow_mul,show (m+1)*2=2*m+1+1 by omega,pow_succ]
    convert hb (2*m+1) hm.right using 1 <;> ring
  refine ⟨2^(m+1), ⟨source_practical (by positivity) (practical_two_pow _),
    source_practical (by positivity) first, source_practical (by positivity) second⟩, ?_⟩
  have hg := (m+1).lt_two_pow_self
  omega

end PracticalTriples
end

section
open PracticalTriples

theorem OMA.solution : type_of% @OMA.S_oeis_a294225.main := by
  apply solution_of_profiles
  · intro m hm
    exact (profile_sound (C := 4266960671228463) (by decide)
      seed_A_verified.1 seed_A_verified.2 hm).2.2
  · intro n hn
    exact (profile_sound (C := 3393375887119295) (by decide)
      seed_B_verified.1 seed_B_verified.2 hn).2.2
end
