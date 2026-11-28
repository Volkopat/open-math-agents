import OMAStatements.S_mo_509919
import Mathlib

/-!
# Sums of squares of the smallest divisors

Tong Lingling asks for finiteness separately at each fixed prefix length k.
OEIS A185584 and A185873 record examples and their prefix lengths. Every listed
example beyond 1 in the September 2026 A185584 entry is even. We verify an odd
example, 227642083294575, with k=23. In every odd solution every prime factor
is itself one of the selected divisors. The file also gives nineteen even
examples absent from the same OEIS listing, including a prefix of length 10798.

Write Ω(n) for the total number of prime factors with multiplicity. If Ω(n) is
at least 2k-1, then n is at most k^(2k-1). When Ω is bounded, only finitely many
solutions of any prefix length have at most one prime factor above a prescribed
cutoff. The conjecture is therefore equivalent to boundedness of the second
largest distinct prime at each fixed multiplicity bound. A separate estimate
bounds every solution all of whose prime factors lie in a moving interval of
prescribed fixed width. A two-prime construction gives a quadratic equation
whose solutions in the prime variables produce genuine examples.

Sources: https://mathoverflow.net/questions/509919, https://oeis.org/A185584,
https://oeis.org/A185873, and the author's small cases at
https://math.stackexchange.com/questions/5062834.
-/

namespace Div509
open OMA.S_mo_509919

/-- Sorting the elements on either side of a cutoff identifies the initial
segment without constructing any divisor above the cutoff. -/
theorem prefix_of_cutoff (s : Finset ℕ) (D : ℕ) :
    s.sort.take ((s.filter (· ≤ D)).card) = (s.filter (· ≤ D)).sort := by
  let lo := (s.filter (· ≤ D)).sort
  let hi := (s.filter (D < ·)).sort
  have hlo (d : ℕ) : d ∈ lo ↔ d ∈ s ∧ d ≤ D := by simp [lo]
  have hhi (d : ℕ) : d ∈ hi ↔ d ∈ s ∧ D < d := by simp [hi]
  have hdis : lo.Disjoint hi := by
    intro d hd hj
    have := (hlo d).mp hd
    have := (hhi d).mp hj
    omega
  have nn : (lo++hi).Nodup := List.nodup_append.mpr
    ⟨Finset.sort_nodup _ _, Finset.sort_nodup _ _, by intro x hx y hy he; exact hdis hx (he ▸ hy)⟩
  have so : (lo++hi).Pairwise (· ≤ ·) := List.pairwise_append.mpr
    ⟨Finset.pairwise_sort _ _, Finset.pairwise_sort _ _, by
      intro d hd e he
      have := (hlo d).mp hd
      have := (hhi e).mp he
      omega⟩
  have heq : (lo++hi).toFinset = s := by
    ext d
    simp only [List.mem_toFinset, List.mem_append, hlo, hhi]
    by_cases h : d ≤ D <;> simp [h, show D < d ↔ ¬ d ≤ D by omega]
  have full := (List.toFinset_sort (· ≤ ·) nn).mpr so
  rw [heq] at full
  rw [full, ←Finset.length_sort (s:=s.filter (· ≤ D)) (· ≤ ·)]
  exact List.take_left

theorem mem_of_cutoff {n k D : ℕ} (hc : (n.divisors.filter (· ≤ D)).card = k)
    (hs : ∑ d ∈ n.divisors.filter (· ≤ D), d^2 = n) :
    k ≤ n.divisors.card ∧ n = sumSqSmallestDivisors k n := by
  refine ⟨hc ▸ Finset.card_filter_le _ _, ?_⟩
  unfold sumSqSmallestDivisors
  rw [←hc, prefix_of_cutoff]
  rw [←List.sum_toFinset _ (Finset.sort_nodup _ _), Finset.sort_toFinset]
  exact hs.symm


theorem sum_le_of_many (k n B : ℕ) (h : k ≤ (n.divisors.filter (· ≤ B)).card) :
    sumSqSmallestDivisors k n ≤ k*B^2 := by
  unfold sumSqSmallestDivisors
  have hbound := List.sum_le_card_nsmul
    (((n.divisors.sort (· ≤ ·)).take k).map (fun d => d^2)) (B^2) (by
      intro x hx
      obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hx
      have hbig := List.take_subset_take_left n.divisors.sort h hd
      rw [prefix_of_cutoff] at hbig
      exact Nat.pow_le_pow_left (Finset.mem_filter.mp ((Finset.mem_sort (· ≤ ·)).mp hbig)).2 2)
  simp only [nsmul_eq_mul, List.length_map, List.length_take] at hbound
  exact hbound.trans (Nat.mul_le_mul_right _ (Nat.min_le_left _ _))

theorem dvd_of_mem_prefix {k n d : ℕ} (h : d ∈ (n.divisors.sort (· ≤ ·)).take k) : d ∣ n :=
  (Nat.mem_divisors.mp ((Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take h))).1

theorem one_mem_prefix {k n : ℕ} (hk : 0 < k) (hn : 0 < n) :
    1 ∈ (n.divisors.sort (· ≤ ·)).take k := by
  have hsingle : n.divisors.filter (· ≤ 1) = {1} := by
    ext d
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨hd,_⟩,h1⟩
      have := Nat.pos_of_dvd_of_pos hd hn
      omega
    · rintro rfl
      exact ⟨⟨one_dvd _, hn.ne'⟩,le_rfl⟩
  have hsmall := prefix_of_cutoff n.divisors 1
  rw [hsingle] at hsmall
  simp only [Finset.card_singleton, Finset.sort_singleton] at hsmall
  exact List.take_subset_take_left (n.divisors.sort (· ≤ ·)) (show 1 ≤ k by omega)
    (show 1 ∈ (n.divisors.sort (· ≤ ·)).take 1 by rw [hsmall]; simp)

end Div509

namespace Div509

/-- Every additional nonunit factor gives a strictly larger set of divisors. -/
lemma length_lt_divisor_count (l : List ℕ) (h : ∀ p ∈ l, 2 ≤ p) :
    l.length < l.prod.divisors.card := by
  induction l with
  | nil => simp
  | cons p l ih =>
    have hp : 2 ≤ p := h p (by simp)
    have hl : ∀ q ∈ l, 2 ≤ q := fun q hq => h q (by simp [hq])
    have hpos : 0 < l.prod := List.prod_pos (fun q hq => by have := hl q hq; omega)
    have hprod : 0 < p*l.prod := Nat.mul_pos (by omega) hpos
    have hstrict : l.prod < p*l.prod := by nlinarith only [Nat.mul_le_mul_right l.prod hp,hpos]
    have hs : l.prod.divisors ⊂ (p*l.prod).divisors := by
      refine Finset.ssubset_iff_subset_ne.mpr ⟨Nat.divisors_subset_of_dvd hprod.ne' (dvd_mul_left _ _),?_⟩
      intro he
      have hm := Nat.mem_divisors_self (p*l.prod) hprod.ne'
      rw [← he] at hm
      exact hstrict.not_ge (Nat.le_of_dvd hpos (Nat.dvd_of_mem_divisors hm))
    simpa only [List.length_cons,List.prod_cons] using
      (show l.length+1 < (p*l.prod).divisors.card by have := ih hl; have := Finset.card_lt_card hs; omega)

/-- If n has at least 2j+1 prime factors with multiplicity, its first j
factors have product U, and there is a prime p with U ≤ p^j and U²p ≤ n. -/
theorem factor_blocks {n j : ℕ} (hn : n ≠ 0) (hj : 2*j+1 ≤ n.primeFactorsList.length) :
    ∃ U p : ℕ, U ∣ n ∧ 0 < U ∧ j < U.divisors.card ∧ U ≤ p^j ∧ U^2*p ≤ n := by
  let l := n.primeFactorsList
  let first := l.take j
  have hlen : first.length = j := List.length_take_of_le (by dsimp only [l]; omega)
  have htail : l.drop j ≠ [] := by
    rw [Ne, List.drop_eq_nil_iff]
    dsimp only [l]; omega
  obtain ⟨p,tail,ht⟩ := List.exists_cons_of_ne_nil htail
  have hd : first ++ p::tail = l := by rw [← ht]; exact List.take_append_drop j l
  have hsort : (first ++ p::tail).Pairwise (· ≤ ·) := hd ▸ (Nat.primeFactorsList_sorted n).pairwise
  have htwo : ∀ q ∈ first ++ p::tail, 2 ≤ q := by
    rw [hd]; exact fun _ hq => (Nat.prime_of_mem_primeFactorsList hq).two_le
  have hF : ∀ q ∈ first, 2 ≤ q := fun q hq => htwo q (List.mem_append_left _ hq)
  have hp : 0 < p := by have := htwo p (by simp); omega
  have hU : 0 < first.prod := List.prod_pos (fun q hq => by have := hF q hq; omega)
  have hn' : first.prod*(p*tail.prod) = n := by
    simpa only [List.prod_append, List.prod_cons] using
      ((congrArg List.prod hd).trans (Nat.prod_primeFactorsList hn))
  have hf : first.prod ≤ p^j := by
    rw [← hlen]
    exact List.prod_le_pow_card first p (fun q hq => (List.pairwise_append.mp hsort).2.2 q hq p (by simp))
  have hL := congrArg List.length hd
  simp only [List.length_append,List.length_cons,hlen] at hL
  have htailLen : j ≤ tail.length := by dsimp only [l] at hL; omega
  have htprod := (Nat.pow_le_pow_right hp htailLen).trans (List.pow_card_le_prod tail p
    (List.pairwise_cons.mp (List.pairwise_append.mp hsort).2.1).1)
  refine ⟨first.prod,p,⟨p*tail.prod,hn'.symm⟩,hU,?_,hf,?_⟩
  · simpa only [← hlen] using length_lt_divisor_count first hF
  · rw [← hn',pow_two]
    nlinarith only [Nat.mul_le_mul_left (p*first.prod) (hf.trans htprod)]

end Div509

namespace Div509
open OMA.S_mo_509919

/-- Any divisor having at least k divisors gives a quadratic row cutoff. -/
theorem subfactor_cutoff {n k u : ℕ} (hn : n ≠ 0) (hu : u ∣ n)
    (hk : k ≤ u.divisors.card) (hw : n = sumSqSmallestDivisors k n) :
    n ≤ k*u^2 := by
  have sub : u.divisors ⊆ n.divisors.filter (· ≤ u) := by
    intro x hx
    have hd := Nat.mem_divisors.mp hx
    exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd.1.trans hu,hn⟩,Nat.le_of_dvd hd.2.bot_lt hd.1⟩
  exact hw ▸ sum_le_of_many k n u (hk.trans (Finset.card_le_card sub))

/-- Whenever a witness has at least 2k-1 prime factors counted with
multiplicities, its entire value is bounded by k^(2k-1). -/
theorem multiplicity_cutoff {n j : ℕ} (hw : n=sumSqSmallestDivisors (j+1) n)
    (hr : 2*j+1 ≤ n.primeFactorsList.length) : n ≤ (j+1)^(2*j+1) := by
  rcases eq_or_ne n 0 with rfl | hn
  · omega
  obtain ⟨u,p,hu,hpos,hcard,hup,hlo⟩ := factor_blocks hn hr
  have hhi := subfactor_cutoff hn hu hcard hw
  have hp : p ≤ j+1 := by
    apply Nat.le_of_mul_le_mul_left (c:=u^2) _ (pow_pos hpos 2)
    simpa only [Nat.mul_comm (j+1) (u^2)] using hlo.trans hhi
  have hupp := hup.trans (Nat.pow_le_pow_left hp j)
  calc
    n ≤ (j+1)*u^2 := hhi
    _ ≤ (j+1)*((j+1)^j)^2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hupp 2)
    _ = _ := by rw [← pow_mul, Nat.mul_comm j 2, pow_succ']

end Div509

namespace Div509
open OMA.S_mo_509919

theorem divisors_at_most_two_pow (n : ℕ) : n.divisors.card ≤ 2^n.primeFactorsList.length := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  let l := n.primeFactorsList.sublists.map List.prod
  have hsub : n.divisors ⊆ l.toFinset := by
    intro x hx
    have hd := Nat.dvd_of_mem_divisors hx
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨x.primeFactorsList,List.mem_sublists.mpr
      (Nat.primeFactorsList_sublist_of_dvd hd hn), Nat.prod_primeFactorsList
        (Nat.pos_of_dvd_of_pos hd hn.bot_lt).ne'⟩
  simpa [l,List.length_sublists] using (Finset.card_le_card hsub).trans (List.toFinset_card_le l)

/-- A prime must divide the positive sum of squares of the selected divisors
which avoid it. Each such divisor divides the complementary factor u. -/
theorem prime_cofactor_bound {n k u p e : ℕ} (hk : 0 < k) (hn : 0 < n)
    (hp : p.Prime) (hpn : p ∣ n) (hfac : n=p^e*u)
    (hw : n=sumSqSmallestDivisors k n) : p ≤ k*u^2 := by
  let l := n.divisors.sort.take k
  let good := l.toFinset.filter (fun x => ¬ p ∣ x)
  let bad := l.toFinset.filter (fun x => p ∣ x)
  have hpart : (∑ x ∈ good, x^2)+(∑ x ∈ bad, x^2)=n := by
    dsimp only [good,bad]
    rw [add_comm,Finset.sum_filter_add_sum_filter_not]
    have hnodup : l.Nodup := (Finset.sort_nodup n.divisors (· ≤ ·)).take
    exact (List.sum_toFinset _ hnodup).trans hw.symm
  have hbad : p ∣ ∑ x ∈ bad, x^2 := Finset.dvd_sum (fun x hx =>
    (Finset.mem_filter.mp hx).2.trans (dvd_pow_self _ (by decide : 2 ≠ 0)))
  have hgood := (Nat.dvd_add_iff_left hbad).mpr (hpart ▸ hpn)
  have hOne : 1 ∈ good := Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr (one_mem_prefix hk hn),hp.not_dvd_one⟩
  have hpos : 0 < ∑ x ∈ good, x^2 := by
    have := Finset.single_le_sum (fun x (_ : x ∈ good) => Nat.zero_le (x^2)) hOne
    simp only [one_pow] at this
    omega
  have hmax : ∑ x ∈ good, x^2 ≤ good.card*u^2 := by
    calc
      _ ≤ ∑ _x ∈ good, u^2 := by
        apply Finset.sum_le_sum
        intro x hx
        obtain ⟨hx,hxp⟩ := Finset.mem_filter.mp hx
        have hx' := dvd_of_mem_prefix (List.mem_toFinset.mp hx)
        have hu : 0 < u := Nat.pos_of_dvd_of_pos (hfac ▸ dvd_mul_left u (p^e)) hn
        rw [hfac] at hx'
        have hc := (hp.coprime_iff_not_dvd.mpr hxp).symm.pow_right e
        exact Nat.pow_le_pow_left (Nat.le_of_dvd hu (hc.dvd_of_dvd_mul_left hx')) 2
      _ = _ := by simp
  have hlen : good.card ≤ k := by
    have h := (Finset.card_filter_le l.toFinset (fun x => ¬ p ∣ x)).trans (List.toFinset_card_le l)
    exact h.trans (by simp [l])
  exact (Nat.le_of_dvd hpos hgood).trans (hmax.trans (Nat.mul_le_mul_right _ hlen))

end Div509

namespace Div509
open OMA.S_mo_509919

lemma strip_one (l : List ℕ) (p P : ℕ) (h : ∀ q ∈ l, q ≠ p → q ≤ P) :
    ∃ e u : ℕ, l.prod=p^e*u ∧ u ≤ (P+1)^l.length := by
  induction l with
  | nil => exact ⟨0,1,by simp,by simp⟩
  | cons q l ih =>
    obtain ⟨e,u,he,hu⟩ := ih (fun x hx => h x (by simp [hx]))
    simp only [List.prod_cons,List.length_cons,pow_succ (P+1),he]
    rcases eq_or_ne q p with rfl | hq
    · exact ⟨e+1,u,by rw [pow_succ]; ring,hu.trans (Nat.le_mul_of_pos_right _ (by omega))⟩
    · exact ⟨e,q*u,by ring,by
        rw [mul_comm q]
        exact Nat.mul_le_mul hu ((h q (by simp) hq).trans (by omega))⟩

/-- Effective row cutoff if all but at most one prime factor belong to a fixed
finite range. The exceptional prime may occur to arbitrary multiplicity up to R. -/
theorem one_large_cutoff {R P n k : ℕ} (hr : n.primeFactorsList.length ≤ R)
    (hk : k ≤ n.divisors.card) (hw : n=sumSqSmallestDivisors k n)
    (hother : ∃ p, ∀ q ∈ n.primeFactorsList, q ≠ p → q ≤ P) :
    n ≤ (P+1+2^R*((P+1)^R)^2)^R := by
  rcases eq_or_ne n 0 with rfl | hn
  · omega
  have hkpos : 0 < k := by
    by_contra! h
    have h0 : k=0 := by omega
    simp [h0,sumSqSmallestDivisors] at hw
    exact hn hw
  obtain ⟨p,hp⟩ := hother
  let C := P+1+2^R*((P+1)^R)^2
  have hC : 0 < C := by dsimp only [C]; omega
  have hsmall (q : ℕ) (hq : q ∈ n.primeFactorsList) : q ≤ C := by
    rcases eq_or_ne q p with rfl | hne
    · obtain ⟨e,u,heu,hu⟩ := strip_one n.primeFactorsList q P hp
      rw [Nat.prod_primeFactorsList hn] at heu
      have hq' := prime_cofactor_bound hkpos hn.bot_lt (Nat.prime_of_mem_primeFactorsList hq)
        (Nat.dvd_of_mem_primeFactorsList hq) heu hw
      have hku := hk.trans ((divisors_at_most_two_pow n).trans (Nat.pow_le_pow_right (by decide) hr))
      have hu' := hu.trans (Nat.pow_le_pow_right (by omega) hr)
      have hle := hq'.trans (Nat.mul_le_mul hku (Nat.pow_le_pow_left hu' 2))
      dsimp only [C]; omega
    · have := hp q hq hne
      dsimp only [C]; omega
  change n ≤ C^R
  calc
    n = n.primeFactorsList.prod := (Nat.prod_primeFactorsList hn).symm
    _ ≤ C^n.primeFactorsList.length := List.prod_le_pow_card _ _ hsmall
    _ ≤ C^R := Nat.pow_le_pow_right hC hr

end Div509

namespace Div509
open OMA.S_mo_509919

/-- Clear the denominator of one large square at a time. The residual is a
positive multiple of 1/A after division by n. -/
lemma residual_bound {n H k : ℕ} (hn : 0 < n) (hH : 0 < H)
    (l : List ℕ) (hs : l.Pairwise (· ≥ ·)) (h1 : 1 ∈ l) (hlen : l.length ≤ k)
    (hdiv : ∀ d ∈ l, d^2 ∣ H*n) (A : ℕ) (hA : 0 < A)
    (hr : n ∣ A*(l.map (fun d => d^2)).sum) :
    n ≤ (2+A*H*k)^(2^l.length) := by
  induction l generalizing A with
  | nil => simp at h1
  | cons d l ih =>
    let s := (l.map (fun x => x^2)).sum
    have hle (x : ℕ) (hx : x ∈ d::l) : x ≤ d := by
      rcases List.mem_cons.mp hx with rfl | hx
      · rfl
      · exact (List.pairwise_cons.mp hs).1 x hx
    have hd : 0 < d := hle 1 h1
    have hsum : d^2+s ≤ k*d^2 := by
      have hh := List.sum_le_card_nsmul ((d::l).map (fun x => x^2)) (d^2)
        (fun x hx => by obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx; exact Nat.pow_le_pow_left (hle i hi) 2)
      simp only [List.length_map,nsmul_eq_mul,Nat.cast_id] at hh
      exact hh.trans (Nat.mul_le_mul_right (d^2) hlen)
    change n ∣ A*(d^2+s) at hr
    have hnA : n ≤ A*(k*d^2) := (Nat.le_of_dvd (Nat.mul_pos hA (by positivity)) hr).trans
      (Nat.mul_le_mul_left _ hsum)
    by_cases he : d=1
    · subst d
      simp only [one_pow,mul_one] at hnA
      have t : A*k ≤ 2+A*H*k := by nlinarith only [Nat.mul_le_mul_right (A*k) hH]
      have hexp : 1 ≤ (2:ℕ)^(1::l).length := Nat.one_le_pow _ _ (by decide : 0 < 2)
      have hh := Nat.pow_le_pow_right (by omega : 0 < 2+A*H*k) hexp
      rw [pow_one] at hh
      exact hnA.trans (t.trans hh)
    · obtain ⟨b,hb⟩ := hdiv d (by simp)
      have hbpos : 0 < b := by by_contra! h; have := Nat.mul_pos hH hn; simp [show b=0 by omega] at hb; omega
      have hbnd : b ≤ H*A*k := by
        apply Nat.le_of_mul_le_mul_left (c:=d^2) _ (pow_pos hd 2)
        rw [← hb]
        calc H*n ≤ H*(A*(k*d^2)) := Nat.mul_le_mul_left _ hnA
             _ = _ := by ring
      have hmul : n ∣ A*b*d^2 := by
        refine ⟨A*H, ?_⟩
        calc A*b*d^2 = A*(d^2*b) := by ring
             _ = _ := by rw [← hb]; ring
      have htot : n ∣ A*b*d^2 + A*b*s := by
        rw [← mul_add, Nat.mul_right_comm A b (d^2+s)]
        exact dvd_mul_of_dvd_left hr b
      have htail : n ∣ (A*b)*s := (Nat.dvd_add_iff_right hmul).mpr htot
      have h := ih (List.pairwise_cons.mp hs).2 (by simpa [he, Ne.symm he] using h1)
        (by simp only [List.length_cons] at hlen; omega)
        (fun x hx => hdiv x (List.mem_cons_of_mem _ hx)) (A*b) (Nat.mul_pos hA hbpos) htail
      have hbase : 2+(A*b)*H*k ≤ (2+A*H*k)^2 := by
        nlinarith only [Nat.mul_le_mul_left (A*H*k) hbnd,Nat.zero_le (A*H*k)]
      apply h.trans
      calc
        _ ≤ ((2+A*H*k)^2)^(2^l.length) := Nat.pow_le_pow_left hbase _
        _ = _ := by rw [← pow_mul,List.length_cons,pow_succ' 2 l.length]

/-- If one multiplier H clears all reduced denominators of d²/n in the
selected prefix, the solution has explicit bounded height. -/
theorem square_denominator_cutoff {n k H : ℕ} (hn : 0 < n) (hk : 0 < k) (hH : 0 < H)
    (hw : n=sumSqSmallestDivisors k n)
    (hdiv : ∀ d ∈ (n.divisors.sort (· ≤ ·)).take k, d^2 ∣ H*n) :
    n ≤ (2+H*k)^(2^k) := by
  let l := n.divisors.sort.take k
  have hs : l.Pairwise (· ≤ ·) := (Finset.pairwise_sort _ _).take
  have hs' : l.reverse.Pairwise (· ≥ ·) := List.pairwise_reverse.mpr hs
  have hlen : l.reverse.length ≤ k := by simp [l]
  have hsum : (l.reverse.map (fun x => x^2)).sum = n := by
    rw [List.map_reverse,List.sum_reverse]
    exact hw.symm
  have hres := residual_bound hn hH l.reverse hs' (by simpa [l] using one_mem_prefix hk hn)
    hlen (fun d hd => hdiv d (by simpa using hd)) 1 (by decide) (by rw [hsum,one_mul])
  simp only [one_mul] at hres
  exact hres.trans (Nat.pow_le_pow_right (by omega) (Nat.pow_le_pow_right (by decide) hlen))

end Div509

namespace Div509
open OMA.S_mo_509919

/-- The fractions d²/n in a solution have total one. Bounding a common
multiplier that makes nH/d² an integer for every selected d is equivalent
to the original finiteness statement. -/
theorem iff_uniform_square_multiplier : (type_of% @OMA.S_mo_509919.main) ↔
    ∀ k : ℕ, ∃ B : ℕ, ∀ n : ℕ, k ≤ n.divisors.card → n=sumSqSmallestDivisors k n →
      ∃ H : ℕ, 0 < H ∧ H ≤ B ∧ ∀ d ∈ (n.divisors.sort (· ≤ ·)).take k, d^2 ∣ H*n := by
  constructor
  · intro h k
    obtain ⟨M,hM⟩ := (h k).bddAbove
    refine ⟨M+1,?_⟩
    intro n hk hw
    rcases eq_or_ne n 0 with rfl | hn
    · exact ⟨1,by decide,by omega,fun _ _ => dvd_zero _⟩
    · have hle : n ≤ M := hM (show n ∈ {n : ℕ | k ≤ n.divisors.card ∧ n=sumSqSmallestDivisors k n} from ⟨hk,hw⟩)
      refine ⟨n,hn.bot_lt,by omega,?_⟩
      intro d hd
      rw [←pow_two n]
      exact pow_dvd_pow_of_dvd (dvd_of_mem_prefix hd) 2
  · intro h k
    obtain ⟨B,hB⟩ := h k
    apply (Set.finite_Iic ((2+B*k)^(2^k))).subset
    rintro n ⟨hkn,hw⟩
    rcases eq_or_ne n 0 with rfl | hn
    · exact Nat.zero_le _
    rcases eq_or_ne k 0 with rfl | hk
    · simp [sumSqSmallestDivisors] at hw
      exact (hn hw).elim
    obtain ⟨H,hH,hHB,hd⟩ := hB n hkn hw
    exact (square_denominator_cutoff hn.bot_lt hk.bot_lt hH hw hd).trans
      (Nat.pow_le_pow_left (by have := Nat.mul_le_mul_right k hHB; omega) _)

end Div509

namespace Div509

lemma cluster_product_bounds (L : List ℕ) {p q : ℕ} (h : ∀ x ∈ L, p ≤ x ∧ x ≤ q) :
    p^L.length ≤ L.prod ∧ L.prod ≤ q^L.length := by
  induction L with
  | nil => simp
  | cons x xs ih =>
    obtain ⟨px,xq⟩ := h x (by simp)
    obtain ⟨h1,h2⟩ := ih (fun y hy => h y (by simp [hy]))
    simp only [List.length_cons,List.prod_cons,pow_succ']
    exact ⟨Nat.mul_le_mul px h1,Nat.mul_le_mul xq h2⟩

lemma cluster_dvd_bounds {n d p q : ℕ} (hn : 0<n) (hd : d∣n)
    (h : ∀ x ∈ n.primeFactorsList, p≤x ∧ x≤q) :
    p^d.primeFactorsList.length ≤ d ∧ d ≤ q^d.primeFactorsList.length := by
  have h0 := Nat.pos_of_dvd_of_pos hd hn
  have hp := cluster_product_bounds d.primeFactorsList
    (fun x hx => h x (Nat.primeFactorsList_subset_of_dvd hd hn.ne' hx))
  simpa only [Nat.prod_primeFactorsList h0.ne'] using hp

/-- If two equal-length products have pairwise ordered factors all at least p,
a strict inequality separates their products by at least p to the penultimate length. -/
lemma separated_products {L R : List ℕ} {p : ℕ} (hlen : L.length=R.length)
    (hlow : ∀ x∈L, p ≤ x) (hord : ∀ x∈L, ∀y∈R, x≤y) :
    L.prod=R.prod ∨ L.prod+p^(L.length-1)≤R.prod := by
  induction L generalizing R with
  | nil => cases R <;> simp_all
  | cons x xs ih =>
    cases R with
    | nil => simp at hlen
    | cons y ys =>
      obtain hxy := hord x (by simp) y (by simp)
      have hx := hlow x (by simp)
      have hxs : ∀ z∈xs,p≤z := fun z hz => hlow z (by simp [hz])
      have hrec := ih (R:=ys) (by simpa using hlen) hxs
        (fun v hv w hw => hord v (by simp [hv]) w (by simp [hw]))
      have hle : xs.prod ≤ ys.prod := by rcases hrec with h|h <;> omega
      simp only [List.prod_cons,List.length_cons,Nat.add_sub_cancel]
      by_cases he : x=y
      · subst y
        rcases hrec with eq | inc
        · exact Or.inl (by rw [eq])
        · right
          cases xs with
          | nil => simp_all
          | cons z zs =>
            simp only [List.length_cons,Nat.add_sub_cancel] at inc ⊢
            have h1 := Nat.mul_le_mul_left x inc
            have h2 := Nat.mul_le_mul_right (p^zs.length) hx
            rw [pow_succ']
            nlinarith only [h1,h2]
      · right
        have low : p^xs.length ≤ xs.prod := by
          have h := cluster_product_bounds xs (p:=p) (q:=xs.sum)
            (fun z hz => ⟨hxs z hz,List.single_le_sum (fun _ _ => Nat.zero_le _) z hz⟩)
          exact h.1
        have h1 := Nat.mul_le_mul (show x+1 ≤ y by omega) hle
        nlinarith only [h1,low]

lemma omega_mul {a b : ℕ} (ha : 0<a) (hb : 0<b) :
    (a*b).primeFactorsList.length = a.primeFactorsList.length+b.primeFactorsList.length := by
  simpa using (Nat.perm_primeFactorsList_mul ha.ne' hb.ne').length_eq

end Div509

namespace Div509

lemma narrow_powers {p q r i : ℕ} (hpq : p≤q) (hi : i≤r) (h : q^r<2*p^r) :
    q^i < 2*p^i := by
  apply Nat.lt_of_mul_lt_mul_right (a:=p^(r-i))
  calc
    q^i*p^(r-i) ≤ q^i*q^(r-i) := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hpq _)
    _ = q^r := by rw [←pow_add]; congr 1; omega
    _ < 2*p^r := h
    _ = (2*p^i)*p^(r-i) := by rw [mul_assoc,←pow_add]; congr 2; omega

lemma cluster_middle_layer {n D k p q r j : ℕ} (hp : 2*k<p) (hk : 0<k)
    (hpq : p≤q) (hnarrow : q^r<2*p^r)
    (hn : p^r≤n ∧ n≤q^r) (hD : p^j≤D ∧ D≤q^j)
    (hs : D^2≤n ∧ n≤k*D^2) : r=2*j := by
  have hp0 : 0<p := by omega
  have hDlo : p^(2*j) ≤ D^2 := by simpa [pow_mul,mul_comm 2 j] using Nat.pow_le_pow_left hD.1 2
  have hDhi : D^2 ≤ q^(2*j) := by simpa [pow_mul,mul_comm 2 j] using Nat.pow_le_pow_left hD.2 2
  rcases lt_trichotomy r (2*j) with lt | eq | gt
  · have h1 := Nat.pow_le_pow_right hp0 (show r+1 ≤ 2*j by omega)
    rw [pow_succ'] at h1
    have h2 := Nat.mul_le_mul_right (p^r) (show 2≤p by omega)
    omega
  · exact eq
  · have h1 := Nat.pow_le_pow_right hp0 (show 2*j+1≤r by omega)
    rw [pow_succ'] at h1
    have h2 := narrow_powers hpq gt.le hnarrow
    have h3 := Nat.mul_lt_mul_of_pos_left h2 hk
    have h4 := Nat.mul_le_mul_right (p^(2*j)) (show 2*k≤p by omega)
    have h5 := Nat.mul_le_mul_left k hDhi
    nlinarith only [h1,h3,h4,h5,hn.1,hs.2]

end Div509

namespace Div509
open OMA.S_mo_509919

/-- A witness has a last selected divisor D. Every smaller divisor is selected and
the contribution of the smaller divisors is bounded term by term. -/
theorem prefix_profile {k n : ℕ} (hk : 2≤k) (hk' : k≤n.divisors.card)
    (hw : n=sumSqSmallestDivisors k n) :
    ∃ D, D∣n ∧ D^2<n ∧ n≤k*D^2 ∧
    (∀ T, T∣n → T<D → T^2+D^2≤n) ∧
    (∀ U, (∀ T, T∣n → T<D → T^2≤U) → n≤D^2+k*U) := by
  have hn : 0<n := by
    by_contra! h
    have h0 : n=0 := Nat.eq_zero_of_le_zero h
    simp [h0] at hk'
    omega
  let l := n.divisors.sort (· ≤ ·)
  let w := l.take k
  have hlen : w.length=k := List.length_take_of_le (by simpa [l] using hk')
  have hne : w≠[] := by intro hh; simp [hh] at hlen; omega
  let L := w.dropLast
  let D := w.getLast hne
  have hsplit : L++[D]=w := List.dropLast_append_getLast hne
  have hsort : l.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hpair : (L++[D]).Pairwise (· ≤ ·) := hsplit ▸ hsort.take
  have hnd : (L++[D]).Nodup := hsplit ▸ (Finset.sort_nodup _ _).take
  have hnD : D∉L := fun hin => (List.nodup_append.mp hnd).2.2 D hin D (by simp) rfl
  have hall (x : ℕ) (hx : x∈w) : x∣n := Nat.dvd_of_mem_divisors
    ((Finset.mem_sort _).mp (List.mem_of_mem_take hx))
  have hdw : D∈w := List.getLast_mem hne
  have hlt (x : ℕ) (hx : x∈L) : x<D := by
    have hle := (List.pairwise_append.mp hpair).2.2 x hx D (by simp)
    exact lt_of_le_of_ne hle (fun he => hnD (he ▸ hx))
  have hdvd (x : ℕ) (hx : x∈L) : x∣n := hall x (hsplit ▸ List.mem_append_left _ hx)
  have hallT (T : ℕ) (htu : T∣n) (ht : T<D) : T∈L := by
    have htmem : T∈l := (Finset.mem_sort _).mpr (Nat.mem_divisors.mpr ⟨htu,hn.ne'⟩)
    rw [←List.take_append_drop k l, List.mem_append] at htmem
    rcases htmem with hin | hout
    · change T∈w at hin
      rw [←hsplit, List.mem_append,List.mem_singleton] at hin
      exact hin.resolve_right ht.ne
    · exact False.elim (ht.not_ge (hsort.rel_of_mem_take_of_mem_drop hdw hout))
  have hsum : n=(L.map (·^2)).sum+D^2 := by
    change n=(w.map (·^2)).sum at hw
    simpa [←hsplit] using hw
  have hLlen : L.length+1=k := by simpa [←hsplit] using hlen
  have hplus (x : ℕ) (hx : x∈L) : x^2 ≤ (L.map (·^2)).sum :=
    List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map_of_mem hx)
  have hneL : L≠[] := by intro hh; simp [hh] at hLlen; omega
  obtain ⟨x,hx⟩ := List.exists_mem_of_ne_nil L hneL
  have xpos := Nat.pos_of_dvd_of_pos (hdvd x hx) hn
  have hpos := hplus x hx
  have xpos' : 0<x^2 := pow_pos xpos _
  refine ⟨D,hall D hdw,by omega,?_,?_,?_⟩
  · have hb := (L.map (·^2)).sum_le_card_nsmul (D^2) (by
      intro v hv
      obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
      exact Nat.pow_le_pow_left (hlt u hu).le _)
    simp only [List.length_map,nsmul_eq_mul] at hb
    change (L.map (·^2)).sum ≤ L.length*D^2 at hb
    rw [←hLlen, Nat.add_mul,one_mul]
    omega
  · intro T hT ht
    have := hplus T (hallT T hT ht)
    omega
  · intro U hu
    have hb := (L.map (·^2)).sum_le_card_nsmul U (by
      intro v hv
      obtain ⟨u,hmem,rfl⟩ := List.mem_map.mp hv
      exact hu u (hdvd u hmem) (hlt u hmem))
    simp only [List.length_map,nsmul_eq_mul] at hb
    change (L.map (·^2)).sum ≤ L.length*U at hb
    have := Nat.mul_le_mul_right U (show L.length≤k by omega)
    omega

end Div509

namespace Div509

/-- Exchanging a larger selected prime for a smaller complementary prime would insert a
second divisor of middle-layer size into the selected prefix. -/
lemma cluster_exchange {n D C p q : ℕ} (hn : 0<n) (hprod : n=D*C)
    (bounds : ∀x∈n.primeFactorsList,p≤x ∧ x≤q)
    (nsmall : n < 2*(p^D.primeFactorsList.length)^2)
    (profile : ∀T, T∣n → T<D → T^2+D^2 ≤ n) :
    ∀x∈D.primeFactorsList, ∀y∈C.primeFactorsList, x≤y := by
  have hd : D∣n := ⟨C,hprod⟩
  have hD := Nat.pos_of_dvd_of_pos hd hn
  have hC : 0<C := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hprod
    omega
  have hb := (cluster_dvd_bounds hn hd bounds).1
  intro x hx y hy
  by_contra! hxy
  obtain ⟨u,hu⟩ := Nat.dvd_of_mem_primeFactorsList hx
  obtain ⟨v,hv⟩ := Nat.dvd_of_mem_primeFactorsList hy
  have ux : 0<u := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hu
    omega
  have xp := Nat.prime_of_mem_primeFactorsList hx
  have yp := Nat.prime_of_mem_primeFactorsList hy
  have hlen : (y*u).primeFactorsList.length = D.primeFactorsList.length := by
    rw [hu, omega_mul yp.pos ux,omega_mul xp.pos ux,Nat.primeFactorsList_prime xp,
      Nat.primeFactorsList_prime yp]
    rfl
  have hdiv : y*u∣n := by
    refine ⟨x*v,?_⟩
    rw [hprod,hu,hv]; ring
  have hsmall : y*u<D := hu ▸ Nat.mul_lt_mul_of_pos_right hxy ux
  have hinc := profile (y*u) hdiv hsmall
  have h2 := (cluster_dvd_bounds hn hdiv bounds).1
  rw [hlen] at h2
  have h3 := Nat.pow_le_pow_left h2 2
  have h4 := Nat.pow_le_pow_left hb 2
  omega

end Div509

namespace Div509
open OMA.S_mo_509919

/-- A large solution cannot have all prime factors in an interval whose endpoints,
raised to the total number of factors with multiplicity, differ by a factor less than two. -/
theorem cluster_exclusion {k n p q : ℕ} (hk : 2≤k) (hp : 2*k<p) (hpq : p≤q)
    (hb : ∀x∈n.primeFactorsList,p≤x ∧ x≤q)
    (hnarrow : q^n.primeFactorsList.length < 2*p^n.primeFactorsList.length)
    (hcard : k ≤ n.divisors.card) : n ≠ sumSqSmallestDivisors k n := by
  intro hw
  obtain ⟨D,hd,hDlt,hupper,hpre,htail⟩ := prefix_profile hk hcard hw
  have hn : 0<n := by omega
  have hD := Nat.pos_of_dvd_of_pos hd hn
  obtain ⟨C,hprod⟩ := hd
  have hd : D∣n := ⟨C,hprod⟩
  have hC : 0<C := by
    by_contra! hc
    simp [Nat.eq_zero_of_le_zero hc] at hprod
    omega
  let r := n.primeFactorsList.length
  let j := D.primeFactorsList.length
  have hpr : 0<p := by omega
  have Hn := cluster_dvd_bounds hn (dvd_refl n) hb
  have HD := cluster_dvd_bounds hn hd hb
  have hr : r=2*j := cluster_middle_layer hp (by omega) hpq hnarrow Hn HD ⟨hDlt.le,hupper⟩
  have hj : 0<j := by
    by_contra! he
    have h0 : r=0 := by omega
    change p^r≤n ∧ n≤q^r at Hn
    rw [h0] at Hn
    have n1 : n=1 := le_antisymm (by simpa using Hn.2) hn
    simp [n1] at hcard
    omega
  have hclose : n < 2*(p^j)^2 := by
    have hlt := Hn.2.trans_lt hnarrow
    change n<2*p^r at hlt
    rw [hr,mul_comm 2 j,pow_mul] at hlt
    exact hlt
  have hEx := cluster_exchange hn hprod hb hclose hpre
  have hlen : D.primeFactorsList.length=C.primeFactorsList.length := by
    have hi := omega_mul hD hC
    rw [←hprod] at hi
    dsimp [r,j] at hr
    omega
  have hh := separated_products hlen
    (fun x hx => (hb x (Nat.primeFactorsList_subset_of_dvd hd hn.ne' hx)).1) hEx
  rw [Nat.prod_primeFactorsList hD.ne',Nat.prod_primeFactorsList hC.ne'] at hh
  have hdc : D+p^(j-1) ≤ C := by
    rcases hh with he | he
    · rw [hprod,←he,pow_two] at hDlt
      omega
    · exact he
  have hlo : D^2 + D*p^(j-1) ≤ n := by
    rw [hprod]
    nlinarith only [Nat.mul_le_mul_left D hdc]
  have hhi := htail (q^(2*(j-1))) (by
    intro T hT hlt
    have ht := cluster_dvd_bounds hn hT hb
    have hdeg : T.primeFactorsList.length<j := by
      by_contra! hbad
      have hb1 := (Nat.pow_le_pow_right hpr hbad).trans ht.1
      have hb2 := Nat.pow_le_pow_left hb1 2
      have hb3 := Nat.pow_le_pow_left HD.1 2
      change (p^j)^2≤D^2 at hb3
      have htpre := hpre T hT hlt
      omega
    have hsmall := ht.2.trans (Nat.pow_le_pow_right (show 0<q by omega) (by omega : T.primeFactorsList.length≤j-1))
    rw [mul_comm 2 (j-1),pow_mul]
    exact Nat.pow_le_pow_left hsmall 2)
  have ht := narrow_powers hpq (show 2*(j-1)≤r by omega) hnarrow
  have h1 := Nat.mul_lt_mul_of_pos_left ht (show 0<k by omega)
  have h2 := Nat.mul_le_mul_right (p^(2*(j-1))) (show 2*k≤p by omega)
  have h3 := Nat.mul_le_mul_right (p^(j-1)) HD.1
  change p^j*p^(j-1)≤D*p^(j-1) at h3
  have hpow : p^j = p*p^(j-1) := by
    conv_lhs => rw [show j=(j-1)+1 by omega,pow_succ']
  rw [hpow] at h3
  simp only [mul_comm 2 (j-1),pow_mul,pow_two] at h1 h2 hhi
  nlinarith only [h1,h2,h3,hlo,hhi]

end Div509

namespace Div509

private lemma binomial_width_bound (p w r : ℕ) (h : r*w≤p) :
    (p+w)^r*(p-r*w) ≤ p^(r+1) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h0 : r*w≤p := by nlinarith only [h,Nat.zero_le w]
    have h1 := ih h0
    have hs : (p+w)*(p-(r+1)*w) ≤ p*(p-r*w) := by
      have h2 := Nat.sub_add_cancel h
      have h3 := Nat.sub_add_cancel h0
      nlinarith only [congrArg (fun x : ℕ => p*x) h2,
        congrArg (fun x : ℕ => p*x) h3,
        Nat.mul_le_mul_left w (Nat.sub_le p ((r+1)*w))]
    have twice := Nat.mul_le_mul_left ((p+w)^r) hs
    have next := Nat.mul_le_mul_left p h1
    rw [pow_succ (p+w),pow_succ p (r+1)]
    nlinarith only [twice,next]

lemma narrow_of_width {p q r : ℕ} (hpq : p≤q) (hw : 2*r*(q-p)<p) :
    q^r < 2*p^r := by
  let w := q-p
  have h : 2*(r*w)<p := by dsimp [w]; simpa only [Nat.mul_assoc] using hw
  have hq : p+w=q := by dsimp [w]; omega
  have b := binomial_width_bound p w r (by omega)
  rw [hq,pow_succ] at b
  have pos : 0<q := by omega
  have comp := Nat.mul_lt_mul_of_pos_left (show p<2*(p-r*w) by omega) (pow_pos pos r)
  apply Nat.lt_of_mul_lt_mul_right (a:=p)
  nlinarith only [comp,b]
end Div509

namespace Div509
open OMA.S_mo_509919

/-- An interval containing all prime factors of a witness, with lower endpoint
larger than 2k, must have relative width at least 1/(4k). -/
theorem relative_prime_spread {k n p q : ℕ} (hk : 2≤k) (hpq : p≤q)
    (hb : ∀x∈n.primeFactorsList,p≤x ∧ x≤q)
    (hcard : k≤n.divisors.card) (hw : n=sumSqSmallestDivisors k n) :
    p≤2*k ∨ p≤4*k*(q-p) := by
  by_contra! hc
  obtain ⟨hbig,hgap⟩ := hc
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have hn : 0<n := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hcard
  have lo := (cluster_dvd_bounds hn (dvd_refl n) hb).1
  let r := n.primeFactorsList.length
  have hr : r < 2*j+1 := by
    by_contra! hlarge
    have hrow := multiplicity_cutoff hw hlarge
    have h1 := Nat.pow_le_pow_right (show 0<p by omega) hlarge
    have h2 := Nat.pow_lt_pow_left (show j+1<p by omega) (show 2*j+1≠0 by omega)
    change p^r≤n at lo
    omega
  have hlin : 2*r*(q-p)<p := (Nat.mul_le_mul_right (q-p) (show 2*r ≤ 4*(j+1) by omega)).trans_lt hgap
  exact cluster_exclusion hk hbig hpq hb (narrow_of_width hpq hlin) hcard hw

/-- For any fixed width W the moving interval of prime factors contributes only
finitely many rows, with an effective bound depending on k and W alone. -/
theorem bounded_prime_diameter {k n p q W : ℕ} (hk : 2≤k) (hpq : p≤q) (hwid : q≤p+W)
    (hb : ∀x∈n.primeFactorsList,p≤x ∧ x≤q)
    (hcard : k≤n.divisors.card) (hw : n=sumSqSmallestDivisors k n) :
    n ≤ (2*k+(4*k+1)*W)^(2*k-1) := by
  have hsp := relative_prime_spread hk hpq hb hcard hw
  have hbq : q ≤ 2*k+(4*k+1)*W := by
    have := Nat.mul_le_mul_left (4*k) (show q-p ≤ W by omega)
    rcases hsp with hp|hp <;> nlinarith
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have he : 2*(j+1)-1=2*j+1 := by omega
  rw [he]
  by_cases hs : 2*j+1≤n.primeFactorsList.length
  · exact (multiplicity_cutoff hw hs).trans
      (Nat.pow_le_pow_left (by omega) _)
  · have hn : 0<n := by
      by_contra! h
      simp [Nat.eq_zero_of_le_zero h] at hcard
    have hu := (cluster_dvd_bounds hn (dvd_refl n) hb).2
    exact hu.trans ((Nat.pow_le_pow_left hbq _).trans (Nat.pow_le_pow_right (by omega) (by omega)))

end Div509

namespace Div509
open OMA.S_mo_509919

private lemma product_square_mod (m : ℕ) (l : List ℕ) :
    l.prod^2 ≡ (l.map (fun x => x^2%m)).prod [MOD m] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.prod_cons,List.map_cons,mul_pow]
    exact (Nat.mod_modEq _ _).symm.mul ih

private lemma sum_mod_of_mem (m : ℕ) (f g : ℕ → ℕ) (l : List ℕ)
    (h : ∀ d∈l, f d ≡ g d [MOD m]) :
    (l.map f).sum ≡ (l.map g).sum [MOD m] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    exact (h x (by simp)).add (ih (fun z hz => h z (by simp [hz])))

/-- Reduction of each prime-factor square modulo any divisor of n gives a new positive
sum, since the contribution of the divisor 1 is always the empty product 1. -/
theorem square_residue_bound {m n k B : ℕ} (hn : 0<n) (hk : 0<k) (hm : m∣n)
    (hb : ∀ x∈n.primeFactorsList, x^2%m≤B) (hw : n=sumSqSmallestDivisors k n) :
    m ≤ k*(max 1 B)^n.primeFactorsList.length := by
  let f := fun d : ℕ => (d.primeFactorsList.map (fun x => x^2%m)).prod
  let l := n.divisors.sort.take k
  have modsum : n ≡ (l.map f).sum [MOD m] := by
    change n=(l.map (·^2)).sum at hw
    rw [hw]
    apply sum_mod_of_mem
    intro d hd
    have pos := Nat.pos_of_dvd_of_pos (dvd_of_mem_prefix hd) hn
    simpa only [Nat.prod_primeFactorsList pos.ne',f] using product_square_mod m d.primeFactorsList
  have hdiv := Nat.modEq_zero_iff_dvd.mp (modsum.symm.trans (Nat.modEq_zero_iff_dvd.mpr hm))
  have hone : 1 ∈ (l.map f) := by
    have hm1 := List.mem_map_of_mem (f:=f) (one_mem_prefix hk hn)
    simpa [f,l] using hm1
  have hpos := List.single_le_sum (fun _ _ => Nat.zero_le _) 1 hone
  have upper := (l.map f).sum_le_card_nsmul ((max 1 B)^n.primeFactorsList.length) (by
    intro y hy
    obtain ⟨d,hd,rfl⟩ := List.mem_map.mp hy
    have sub := Nat.primeFactorsList_sublist_of_dvd (dvd_of_mem_prefix hd) hn.ne'
    have hprod := List.prod_le_pow_card (d.primeFactorsList.map (fun x => x^2%m)) (max 1 B) (by
      intro z hz
      obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hz
      exact (hb x (sub.subset hx)).trans (le_max_right _ _))
    simp only [List.length_map] at hprod
    exact hprod.trans (Nat.pow_le_pow_right (by omega) sub.length_le))
  simp only [List.length_map,nsmul_eq_mul] at upper
  change (l.map f).sum ≤ l.length*(max 1 B)^n.primeFactorsList.length at upper
  have hlen : l.length≤k := by simp [l]
  exact (Nat.le_of_dvd hpos hdiv).trans (upper.trans (Nat.mul_le_mul_right _ hlen))

/-- The representatives can have either sign before squaring. -/
theorem signed_residue_bound {m n k B : ℕ} (hn : 0<n) (hk : 0<k) (hm : m∣n)
    (hb : ∀ x∈n.primeFactorsList, ∃ b≤B, x^2 ≡ b^2 [MOD m])
    (hw : n=sumSqSmallestDivisors k n) : m ≤ k*(max 1 B)^(2*n.primeFactorsList.length) := by
  have h := square_residue_bound hn hk hm (B:=(max 1 B)^2) (fun x hx => by
    obtain ⟨b,hb',hc⟩ := hb x hx
    rw [show x^2%m=b^2%m from hc]
    exact (Nat.mod_le _ _).trans (Nat.pow_le_pow_left (hb'.trans (le_max_right _ _)) _)) hw
  have hpos : 1≤(max 1 B)^2 := Nat.one_le_pow _ _ (by omega)
  simpa only [max_eq_right hpos,pow_mul] using h
end Div509

namespace Div509
open OMA.S_mo_509919

/-- Finiteness still holds for several moving groups of prime factors, provided each
prime lies within W of one of 0,m,2m,...,A*m for a common divisor m of the solution. -/
theorem affine_prime_cutoff {k n m A W : ℕ} (hk : 2 ≤ k)
    (hcard : k≤n.divisors.card) (hm : m∣n)
    (hf : ∀ x∈n.primeFactorsList, ∃ a≤A, ∃ b≤W, x=a*m+b ∨ x+b=a*m)
    (hw : n=sumSqSmallestDivisors k n) :
    n ≤ max (k^(2*k-1))
      ((A*(k*(max 1 W)^(2*(2*k-1)))+W)^(2*k-1)) := by
  obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k≠0)
  have he : 2*(j+1)-1=2*j+1 := by omega
  rw [he]
  by_cases high : 2*j+1 ≤ n.primeFactorsList.length
  · exact (multiplicity_cutoff hw high).trans (le_max_left _ _)
  have hn : 0<n := by
    by_contra! h
    simp [Nat.eq_zero_of_le_zero h] at hcard
  have hmcap := signed_residue_bound hn (by omega : 0<j+1) hm (B:=W) (fun x hx => by
    obtain ⟨a,_,b,bW,hb⟩ := hf x hx
    refine ⟨b,bW,(ZMod.natCast_eq_natCast_iff _ _ _).mp ?_⟩
    push_cast
    rcases hb with rfl|heq
    · simp
    · have hz := congrArg (fun z : ℕ => (z : ZMod m)) heq
      push_cast at hz
      have hz' : (x : ZMod m)+(b : ZMod m)=0 := by simpa using hz
      rw [eq_neg_of_add_eq_zero_left hz',neg_sq]) hw
  let M := (j+1)*(max 1 W)^(2*(2*j+1))
  have hM : m≤M := hmcap.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega)))
  let U := A*M+W
  have hU : n≤U^n.primeFactorsList.length := (cluster_dvd_bounds hn (dvd_refl n) (p:=0) (q:=U) (by
    intro x hx
    obtain ⟨a,ha,b,hb,heq⟩ := hf x hx
    have hmul := Nat.mul_le_mul ha hM
    exact ⟨Nat.zero_le _,by dsimp [U]; rcases heq with heq|heq <;> omega⟩)).2
  have hUpos : 0<U := by
    by_contra! h
    have U0 := Nat.eq_zero_of_le_zero h
    have n1 : n=1 := by
      cases hh : n.primeFactorsList.length with
      | zero => simp [hh] at hU; omega
      | succ r => simp [U0,hh] at hU; omega
    simp [n1] at hcard
    omega
  exact (hU.trans (Nat.pow_le_pow_right hUpos (by omega : n.primeFactorsList.length≤2*j+1))).trans (le_max_right _ _)
end Div509

namespace Div509
open OMA.S_mo_509919

theorem cutoff_mul_prime {u p D : ℕ} (hu : 0<u) (hp : p.Prime) (hd : D<p) :
    (u*p).divisors.filter (·≤D) = u.divisors.filter (·≤D) := by
  ext d
  simp only [Finset.mem_filter, Nat.mem_divisors]
  constructor
  · rintro ⟨⟨dvd, _⟩, bound⟩
    have pos := Nat.pos_of_dvd_of_pos dvd (Nat.mul_pos hu hp.pos)
    have cop := (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt pos (bound.trans_lt hd))).symm
    exact ⟨⟨cop.dvd_of_dvd_mul_right dvd, hu.ne'⟩,bound⟩
  · rintro ⟨⟨dvd, _⟩, bound⟩
    exact ⟨⟨dvd.trans (dvd_mul_right _ _), (Nat.mul_pos hu hp.pos).ne'⟩, bound⟩

theorem solution_from_core {u p D k : ℕ} (hu : 0<u) (hp : p.Prime) (hd : D<p)
    (hc : (u.divisors.filter (·≤D)).card=k)
    (hs : ∑ d ∈ u.divisors.filter (·≤D), d^2=u*p) :
    k ≤ (u*p).divisors.card ∧ u*p=sumSqSmallestDivisors k (u*p) := by
  apply mem_of_cutoff (D:=D) <;> rw [cutoff_mul_prime hu hp hd] <;> assumption

theorem sum_divisors_coprime {u v : ℕ} (h : u.Coprime v) (f : ℕ → ℕ) :
    ∑ d ∈ (u*v).divisors, f d = ∑ a ∈ u.divisors, ∑ b ∈ v.divisors, f (a*b) := by
  rw [h.divisors_mul, Finset.sum_map]
  change ∑ x ∈ (u.divisors ×ˢ v.divisors).attach, (fun t : ℕ × ℕ => f (t.1*t.2)) x.val = _
  rw [Finset.sum_attach _ (fun t : ℕ × ℕ => f (t.1*t.2)), Finset.sum_product]

theorem core_cutoff_certificate {n k D : ℕ}
    (hc : ∑ d ∈ n.divisors, (if d≤D then 1 else 0) = k)
    (hs : ∑ d ∈ n.divisors, (if d≤D then d^2 else 0) = n) :
    k ≤ n.divisors.card ∧ n=sumSqSmallestDivisors k n := by
  apply mem_of_cutoff (D:=D)
  · rw [←hc, ←Finset.sum_filter]
    simp
  · rw [Finset.sum_filter]
    exact hs

end Div509

namespace Div509
open OMA.S_mo_509919

theorem inverse_moment {u r : ℕ} (hu : 0<u) (hr : 0<r) (e : ℕ) :
    (∑ d ∈ u.divisors.filter (·≤u/r), d^e) +
    (∑ j ∈ (Finset.range r).filter (·∣u), (u/j)^e) = ArithmeticFunction.sigma e u := by
  have heq : u.divisors.filter (·<r) = (Finset.range r).filter (·∣u) := by
    ext j
    simp [Nat.mem_divisors, hu.ne', and_comm]
  have upper :
      (∑ d ∈ u.divisors.filter (u/r<·), d^e) =
      ∑ j ∈ (Finset.range r).filter (·∣u), (u/j)^e := by
    rw [Finset.sum_filter, ←Nat.sum_div_divisors u (fun d => if u/r<d then d^e else 0)]
    rw [←heq, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro j hj
    have hjd := Nat.dvd_of_mem_divisors hj
    have hpos : 0 < u/j := Nat.div_pos (Nat.le_of_dvd hu hjd) (Nat.pos_of_mem_divisors hj)
    have htest : u/r < u/j ↔ j < r := by
      rw [Nat.div_lt_iff_lt_mul hr]
      conv_lhs => lhs; rw [←Nat.div_mul_cancel hjd]
      exact Nat.mul_lt_mul_left hpos
    simp [htest]
  rw [←upper, ArithmeticFunction.sigma_apply, ←Finset.sum_filter_add_sum_filter_not
    u.divisors (fun d => d≤u/r) (fun d => d^e)]
  simp only [not_le]

theorem solution_from_complements {u p r k : ℕ} (hu : 0<u) (hp : p.Prime) (hr : 0<r)
    (hd : u/r < p)
    (hc : ArithmeticFunction.sigma 0 u =
      k + ((Finset.range r).filter (·∣u)).card)
    (hs : ArithmeticFunction.sigma 2 u =
      u*p + ∑ j ∈ (Finset.range r).filter (·∣u), (u/j)^2) :
    k ≤ (u*p).divisors.card ∧ u*p = sumSqSmallestDivisors k (u*p) := by
  apply solution_from_core (D:=u/r) hu hp hd
  · have h := inverse_moment hu hr 0
    simp at h
    omega
  · have h := inverse_moment hu hr 2
    omega

theorem proper_solution {u p : ℕ} (hu : 0<u) (hp : p.Prime) (hd : u/2<p)
    (hs : ArithmeticFunction.sigma 2 u = u*p + u^2) :
    (u.divisors.card-1) ≤ (u*p).divisors.card ∧
    u*p = sumSqSmallestDivisors (u.divisors.card-1) (u*p) := by
  have small : (Finset.range 2).filter (·∣u) = {1} := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨hj, h⟩
      have := Nat.pos_of_dvd_of_pos h hu
      omega
    · rintro rfl
      exact ⟨by decide,one_dvd _⟩
  apply solution_from_complements hu hp (r:=2) (by decide) hd
  · rw [ArithmeticFunction.sigma_zero_apply,small, Finset.card_singleton]
    have hcard := Finset.card_pos.mpr ⟨u,Nat.mem_divisors_self _ hu.ne'⟩
    omega
  · simpa [small] using hs

end Div509

namespace Div509

theorem prime_from_factors (p g : ℕ) (F : List ℕ) (hp : F.prod=p-1)
    (hf : ∀ q∈F, Nat.Prime q)
    (h1 : npowBinRec (p-1) (g : ZMod p) = 1)
    (h2 : F.all (fun q => decide (npowBinRec ((p-1)/q) (g : ZMod p) ≠ 1)) = true) :
    p.Prime := by
  have bin (n : ℕ) : npowBinRec n (g : ZMod p) = (g : ZMod p)^n := by
    induction n with
    | zero => simp [npowBinRec_zero]
    | succ n ih => rw [npowBinRec_succ, ih, pow_succ]
  apply lucas_primality p (g : ZMod p) ((bin _).symm.trans h1)
  intro q hq hd
  rw [←hp] at hd
  have mem := mem_list_primes_of_dvd_prod (Nat.prime_iff.mp hq)
    (fun t ht => Nat.prime_iff.mp (hf t ht)) hd
  simpa only [bin, decide_eq_true_eq] using List.all_eq_true.mp h2 q mem

end Div509

namespace Div509

/-- Below `p*q`, all divisors of `C*p*q` lie in the three indicated copies
of the divisors of `C`. The two primes need not be coprime to `C`. -/
theorem two_prime_cutoff_mem (C p q D x : ℕ) (hC : 0<C) (hp : p.Prime) (hq : q.Prime)
    (hD : D<p*q) :
    x ∈ (C*p*q).divisors.filter (· ≤ D) ↔ x ≤ D ∧ ∃ z ∈ C.divisors, x=z ∨ x=z*p ∨ x=z*q := by
  have hn := (Nat.mul_pos (Nat.mul_pos hC hp.pos) hq.pos).ne'
  simp only [Finset.mem_filter, Nat.mem_divisors, hn, hC.ne', ne_eq, not_false_eq_true,
    and_true]
  constructor
  · rintro ⟨hd,hx⟩
    rw [Nat.mul_assoc] at hd
    obtain ⟨z,b,hz,hb,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hd
    obtain ⟨b₁,b₂,h₁,h₂,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul hb
    refine ⟨hx,z,hz,?_⟩
    have hz' : 0<z := Nat.pos_of_dvd_of_pos hz hC
    rcases (Nat.dvd_prime hp).mp h₁ with rfl|rfl <;> rcases (Nat.dvd_prime hq).mp h₂ with rfl|rfl <;> simp_all
    exact False.elim (hD.not_ge ((Nat.le_mul_of_pos_left _ hz').trans hx))
  · rintro ⟨hx,z,hz,hz'⟩
    refine ⟨?_,hx⟩
    obtain rfl|rfl|rfl := hz'
    · exact dvd_mul_of_dvd_left (dvd_mul_of_dvd_left hz _) _
    · exact dvd_mul_of_dvd_left (Nat.mul_dvd_mul_right hz _) _
    · exact Nat.mul_dvd_mul_right (dvd_mul_of_dvd_left hz _) _

theorem two_prime_cutoff_eq (C p q D : ℕ) (hC : 0<C) (hp : p.Prime) (hq : q.Prime)
    (hD : D<p*q) : (C*p*q).divisors.filter (· ≤ D) =
    ((C.divisors ∪ C.divisors.image (· * p) ∪ C.divisors.image (· * q)).filter (· ≤ D)) := by
  ext x
  rw [two_prime_cutoff_mem C p q D x hC hp hq hD]
  simp only [Finset.mem_filter,Finset.mem_union,Finset.mem_image]
  grind

end Div509

namespace Div509

/-- Splitting the divisor cutoff into a core, a `p`-part, and a `q`-part turns
its square sum into an inhomogeneous binary quadratic form. -/
theorem two_prime_square_sum {C p q D : ℕ} (hC : 0<C) (hcp : C<p) (hpq : p<q)
    (hp : p.Prime) (hq : q.Prime) (hCD : C≤D) (hD : D<p*q) :
    (∑ x ∈ (C*p*q).divisors.filter (· ≤ D), x^2) =
      (∑ r ∈ C.divisors, r^2) + p^2*(∑ r ∈ C.divisors.filter (fun r => r*p≤D), r^2) +
      q^2*(∑ r ∈ C.divisors.filter (fun r => r*q≤D), r^2) := by
  classical
  let S := C.divisors
  let P := (S.filter (fun r => r*p≤D)).image (· * p)
  let Q := (S.filter (fun r => r*q≤D)).image (· * q)
  have eq : (C*p*q).divisors.filter (· ≤ D) = S ∪ P ∪ Q := by
    ext x
    rw [two_prime_cutoff_mem C p q D x hC hp hq hD]
    simp only [S,P,Q,Finset.mem_union,Finset.mem_image,Finset.mem_filter]
    have small (r : ℕ) (hr : r ∈ C.divisors) : r≤D := (Nat.le_of_dvd hC (Nat.dvd_of_mem_divisors hr)).trans hCD
    grind
  have dis (v : ℕ) (hv : C<v) : Disjoint S ((S.filter (fun r => r*v≤D)).image (· * v)) := by
    apply Finset.disjoint_left.mpr
    intro y hy hiy
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp hiy
    have hrp := Nat.pos_of_mem_divisors (Finset.mem_filter.mp hr).1
    exact hv.not_ge ((Nat.le_mul_of_pos_left _ hrp).trans (Nat.le_of_dvd hC (Nat.dvd_of_mem_divisors hy)))
  have disPQ : Disjoint P Q := by
    apply Finset.disjoint_left.mpr
    intro y h1 h2
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨t,ht,he⟩ := Finset.mem_image.mp h2
    have hd : p ∣ t*q := he ▸ dvd_mul_left p r
    have nt : ¬p ∣ t := fun h => hcp.not_ge ((Nat.le_of_dvd (Nat.pos_of_mem_divisors (Finset.mem_filter.mp ht).1) h).trans (Nat.le_of_dvd hC (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp ht).1)))
    exact hpq.ne ((Nat.prime_dvd_prime_iff_eq hp hq).mp ((hp.dvd_mul.mp hd).resolve_left nt))
  have weighted (v : ℕ) (hv : 0<v) :
      (∑ x ∈ (S.filter (fun r => r*v≤D)).image (· * v), x^2) =
      v^2 * ∑ r ∈ S.filter (fun r => r*v≤D), r^2 := by
    rw [Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_right hv hxy),Finset.mul_sum]
    exact Finset.sum_congr rfl (fun _ _ => by ring)
  rw [eq, Finset.sum_union (Finset.disjoint_union_left.mpr ⟨dis q (hcp.trans hpq),disPQ⟩),
    Finset.sum_union (dis p hcp),weighted p hp.pos,weighted q hq.pos]

end Div509

namespace Div509

set_option maxRecDepth 50000 in
/-- The first 23 divisors of this odd integer end at `75*174989`. -/
theorem odd_example : 23 ≤ (227642083294575 : ℕ).divisors.card ∧
    227642083294575 = OMA.S_mo_509919.sumSqSmallestDivisors 23 227642083294575 := by
  have hp : Nat.Prime 174989 := by norm_num
  have hq : Nat.Prime 178817 := by norm_num
  have cut := two_prime_cutoff_eq 7275 174989 178817 13124175 (by decide) hp hq (by decide)
  norm_num1 at cut
  have d : Nat.divisors 7275 = ([1,3,5,15,25,75,97,291,485,1455,2425,7275] : List ℕ).toFinset := by decide +kernel
  rw [d] at cut
  apply mem_of_cutoff (D:=13124175)
  · rw [cut]; decide +kernel
  · rw [cut]; decide +kernel

end Div509

namespace Div509

theorem divisors_times_prime (C p : ℕ) (hC : 0<C) (hp : p.Prime) :
    (C*p).divisors = C.divisors ∪ C.divisors.image (· * p) := by
  ext d
  simp only [Finset.mem_union, Finset.mem_image, Nat.mem_divisors, (Nat.mul_pos hC hp.pos).ne',
    hC.ne',ne_eq,not_false_eq_true,and_true]
  constructor
  · intro h
    obtain ⟨r,s,hr,hs,rfl⟩ := exists_dvd_and_dvd_of_dvd_mul h
    obtain rfl|rfl := (Nat.dvd_prime hp).mp hs
    · simpa using Or.inl hr
    · exact Or.inr ⟨_,hr,rfl⟩
  · rintro (ht|⟨r,hr,rfl⟩)
    · exact dvd_mul_of_dvd_left ht _
    · exact Nat.mul_dvd_mul_right hr _

set_option maxRecDepth 50000 in
theorem example_116 : 116 ≤ (243129606043348872 : ℕ).divisors.card ∧
    243129606043348872 = OMA.S_mo_509919.sumSqSmallestDivisors 116 243129606043348872 := by
  have hp : Nat.Prime 112289 := by norm_num
  have hq : Nat.Prime 8430727 := by norm_num
  have cut := two_prime_cutoff_eq 256824 112289 8430727 202337448 (by decide) hp hq (by decide)
  norm_num1 at cut
  have d : Nat.divisors 6264 = ([1, 2, 3, 4, 6, 8, 9, 12, 18, 24, 27, 29, 36, 54, 58, 72, 87, 108, 116, 174, 216, 232, 261, 348, 522, 696, 783, 1044, 1566, 2088, 3132, 6264] : List ℕ).toFinset := by decide +kernel
  have h : Nat.divisors 256824 = _ := divisors_times_prime 6264 41 (by decide) (by decide)
  rw [h,d] at cut
  apply mem_of_cutoff (D:=202337448)
  · rw [cut]; decide +kernel
  · rw [cut]; decide +kernel

end Div509

namespace Div509
open OMA.S_mo_509919

set_option maxRecDepth 50000 in
/-- The exact binary quadratic equation for the odd 23-divisor template. -/
theorem chamber_7275 {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hC : 7275<p)
    (hlo : p<q) (hhi : 5*q<6*p) :
    (23 ≤ (7275*p*q).divisors.card ∧ 7275*p*q = sumSqSmallestDivisors 23 (7275*p*q)) ↔
       7275*p*q = 61259100 + 6510*p^2 + 885*q^2 := by
  let s : List ℕ := [1,3,5,15,25,75,97,291,485,1455,2425,7275,p,q,3*p,3*q,5*p,5*q,15*p,15*q,25*p,25*q,75*p]
  have hdiv : Nat.divisors 7275 = ([1, 3, 5, 15, 25, 75, 97, 291, 485, 1455, 2425, 7275] : List ℕ).toFinset := by decide +kernel
  have hD : 75*p<p*q := by rw [Nat.mul_comm p q]; exact Nat.mul_lt_mul_of_pos_right (by omega) hp.pos
  have cut : (7275*p*q).divisors.filter (·≤75*p) = s.toFinset := by
    ext v
    rw [two_prime_cutoff_mem 7275 p q (75*p) v (by decide) hp hq hD,hdiv]
    simp only [s,List.mem_toFinset,List.mem_cons,List.not_mem_nil,or_false]
    constructor
    · rintro ⟨hv,z,hz,he⟩
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rcases he with rfl|rfl|rfl <;> omega
    · intro hv
      rcases hv with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;>
        refine ⟨by omega, ?_⟩ <;> first
        | exact ⟨1, by omega, by omega⟩
        | exact ⟨3, by omega, by omega⟩
        | exact ⟨5, by omega, by omega⟩
        | exact ⟨15, by omega, by omega⟩
        | exact ⟨25, by omega, by omega⟩
        | exact ⟨75, by omega, by omega⟩
        | exact ⟨97, by omega, by omega⟩
        | exact ⟨291, by omega, by omega⟩
        | exact ⟨485, by omega, by omega⟩
        | exact ⟨1455, by omega, by omega⟩
        | exact ⟨2425, by omega, by omega⟩
        | exact ⟨7275, by omega, by omega⟩
  have hn : s.Nodup := by
    apply List.SortedLT.nodup
    rw [List.sortedLT_iff_isChain]
    simp only [s, List.isChain_cons_cons, List.isChain_singleton, and_true]
    omega
  have hc : ((7275*p*q).divisors.filter (·≤75*p)).card=23 := by
    rw [cut,List.toFinset_card_of_nodup hn];rfl
  have hs : (∑ x ∈ (7275*p*q).divisors.filter (·≤75*p), x^2) = 61259100 + 6510*p^2 + 885*q^2 := by
    rw [cut, List.sum_toFinset _ hn]
    simp only [s,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil]
    ring
  constructor
  · intro H
    have V := H.2
    unfold sumSqSmallestDivisors at V
    rw [← hc,prefix_of_cutoff,← List.sum_toFinset _ (Finset.sort_nodup _ _),Finset.sort_toFinset,hs] at V
    exact V
  · intro H
    exact mem_of_cutoff hc (hs.trans H.symm)

end Div509

namespace Div509

/-- A positive determinant-one recurrence returns to its initial pair of residues
arbitrarily far along every modulus, retaining any invariant of the recurrence. -/
theorem matrix_modular_lift (a b c d s t L M : ℕ) (hL : 0<L) (hs : 0<s) (ha : 1<a)
    (hdet : a*d=b*c+1) (good : ℕ → ℕ → Prop) (seed : good s t)
    (step : ∀ x y, good x y → good (a*x+b*y) (c*x+d*y)) :
    ∃ x y : ℕ, M<x ∧ good x y ∧ x ≡ s [MOD L] ∧ y ≡ t [MOD L] := by
  let : NeZero L := ⟨hL.ne'⟩
  let F (z : ℕ × ℕ) : ℕ × ℕ := (a*z.1+b*z.2,c*z.1+d*z.2)
  let red (z : ℕ × ℕ) : ZMod L × ZMod L := (z.1,z.2)
  have hd : (a:ZMod L)*d=(b:ZMod L)*c+1 := by
    simpa only [Nat.cast_mul,Nat.cast_add,Nat.cast_one] using congrArg (Nat.cast : ℕ → ZMod L) hdet
  let E : Equiv.Perm (ZMod L × ZMod L) :=
    { toFun := fun z => (a*z.1+b*z.2,c*z.1+d*z.2)
      invFun := fun z => (d*z.1-b*z.2,a*z.2-c*z.1)
      left_inv := by
        rintro ⟨x,y⟩
        apply Prod.ext <;> dsimp only
        · linear_combination x*hd
        · linear_combination y*hd
      right_inv := by
        rintro ⟨x,y⟩
        apply Prod.ext <;> dsimp only
        · linear_combination x*hd
        · linear_combination y*hd }
  have run : Function.Semiconj red F E := by
    rintro ⟨x,y⟩
    simp [red,F,E]
  let N := orderOf E * (M+1)
  have period : E^N=1 := by dsimp only [N]; rw [pow_mul,pow_orderOf_eq_one,one_pow]
  have reduction := run.iterate_right N (s,t)
  rw [← Equiv.Perm.coe_pow, period] at reduction
  have cond (n : ℕ) : good (F^[n] (s,t)).1 (F^[n] (s,t)).2 ∧ s+n ≤ (F^[n] (s,t)).1 := by
    induction n with
    | zero => exact ⟨seed,by simp⟩
    | succ n ih =>
      rw [Function.iterate_succ_apply']
      refine ⟨step _ _ ih.1,?_⟩
      let z := F^[n] (s,t)
      change s+(n+1) ≤ a*z.1+b*z.2
      have hi := ih.2
      change s+n ≤ z.1 at hi
      have mul := Nat.mul_le_mul_right z.1 ha
      omega
  have hN : M < s+N := by
    have hp : 0<orderOf E := orderOf_pos E
    have hle : M+1 ≤ N := Nat.le_mul_of_pos_left _ hp
    omega
  have r₁ := congrArg Prod.fst reduction
  have r₂ := congrArg Prod.snd reduction
  refine ⟨_,_,hN.trans_le (cond N).2,(cond N).1,?_,?_⟩
  · exact (ZMod.natCast_eq_natCast_iff ..).mp r₁
  · exact (ZMod.natCast_eq_natCast_iff ..).mp r₂

end Div509

namespace Div509

set_option maxRecDepth 10000 in
/-- The exact quadratic equation has unbounded solutions congruent to both of the
prime coordinates of the odd example, for every chosen modulus. -/
theorem binary_form_congruent (M L : ℕ) (hL : 0<L) : ∃ p q : ℕ, M<p ∧ 7275<p ∧
    p<q ∧ 5*q<6*p ∧ p ≡ 174989 [MOD L] ∧ q ≡ 178817 [MOD L] ∧
    7275*p*q = 61259100+6510*p^2+885*q^2 := by
  let u : ℕ := 1059226803927211606314844507190249071529030718080103615490272049850624207471951796808892594076168902408186580458221040778760310833317259784372031281637408267753553376946323535886716091783426377258525739898966717975
  let v : ℕ := 2906620213778279502649105436370393876744187949997963905064050118140306418135706345094095040430038656996038227217943131900168191096991081729929948721565346792297585577875452157855200608592729725955802882178259132
  let good (x y : ℕ) := 0<y ∧ 1576*x^2+287*x*y=4083940+8*y^2
  have hseed : good 3828 155849 := by decide +kernel
  have step (x y : ℕ) (h : good x y) : good ((u-287*v)*x+16*v*y) (3152*v*x+(u+287*v)*y) := by
    have hu : 0<u := by decide +kernel
    have yp := Nat.mul_pos (show 0<u+287*v by omega) h.1
    refine ⟨by omega,?_⟩
    have hh := h.2
    dsimp only [u,v]
    norm_num1
    linear_combination hh
  have sol := matrix_modular_lift (u-287*v) (16*v) (3152*v) (u+287*v) 3828 155849 L (M+7275)
    hL (by decide) (by decide +kernel) (by decide +kernel) good hseed step
  obtain ⟨x,y,hx,⟨hy,he⟩,xm,ym⟩ := sol
  refine ⟨5*x+y,6*x+y,by omega,by omega,by omega,by omega,?_,?_,?_⟩
  · exact (xm.mul_left 5).add ym
  · exact (xm.mul_left 6).add ym
  · nlinarith only [he]

end Div509

namespace Div509

theorem odd_local_moment {p q a : ℕ} (hp : p.Prime) (hq : 2≤q) (ha : 0<a)
    (hodd : Odd (a+1)) (hbig : 2*q^a < p) :
    ¬p ∣ ∑ i ∈ Finset.range (a+1), q^(i*2) := by
  intro hdiv
  have qpos : 0<q := by omega
  have tpos : 0<q^a := pow_pos qpos _
  have qle : q≤q^a := by simpa using Nat.pow_le_pow_right qpos (show 1≤a by omega)
  have qsmall : q+1<p := by omega
  have hx : 1<q^(a+1) := one_lt_pow₀ (by omega) (by omega)
  have hm : (∑ i ∈ Finset.range (a+1), q^(i*2))*(q^2-1)=(q^(a+1))^2-1 := by
    calc _ = (∑ i ∈ Finset.range (a+1), (q^2)^i)*(q^2-1) := by
               simp only [←pow_mul, mul_comm 2]
         _ = (q^2)^(a+1)-1 := geom_sum_mul_of_one_le (Nat.succ_le_of_lt (pow_pos qpos 2)) _
         _ = _ := by rw [←pow_mul, ←pow_mul, mul_comm 2]
  have split : (q^(a+1))^2-1 = (q^(a+1)-1)*(q^(a+1)+1) := by
    have y : 1≤q^(a+1) := by omega
    have z : 1≤(q^(a+1))^2 := Nat.succ_le_of_lt (pow_pos (by omega) _)
    nlinarith [Nat.sub_add_cancel y, Nat.sub_add_cancel z]
  obtain left | right := hp.dvd_mul.mp ((hm.trans split) ▸ (hdiv.trans (dvd_mul_right _ _)))
  · obtain ⟨v,hv⟩ := Nat.sub_one_dvd_pow_sub_one q (a+1)
    rw [hv] at left
    have hd := (hp.dvd_mul.mp left).resolve_left
      (Nat.not_dvd_of_pos_of_lt (by omega : 0<q-1) (by omega))
    have vp : 0<v := by
      by_contra! h
      rw [show v=0 by omega, mul_zero] at hv
      omega
    have vl : v≤2*q^a := by
      refine Nat.le_of_mul_le_mul_left (c:=q-1) ?_ (by omega)
      calc (q-1)*v = q^(a+1)-1 := hv.symm
           _ ≤ q^a*q := by rw [pow_succ]; omega
           _ ≤ q^a*(2*(q-1)) := Nat.mul_le_mul_left _ (by omega)
           _ = (q-1)*(2*q^a) := by ring
    exact (Nat.not_dvd_of_pos_of_lt vp (vl.trans_lt hbig)) hd
  · obtain ⟨v,hv⟩ := hodd.nat_add_dvd_pow_add_pow q 1
    simp only [one_pow] at hv
    rw [hv] at right
    have hd := (hp.dvd_mul.mp right).resolve_left
      (Nat.not_dvd_of_pos_of_lt (by omega) qsmall)
    have vp : 0<v := by
      by_contra! h
      rw [show v=0 by omega, mul_zero] at hv
      omega
    have vl : v≤q^a := by
      refine Nat.le_of_mul_le_mul_left (c:=q+1) ?_ (by omega)
      rw [←hv, pow_succ]
      nlinarith
    exact (Nat.not_dvd_of_pos_of_lt vp (by omega)) hd

theorem odd_full_prime_impossible {u p : ℕ} (hu : Odd u) (hp : p.Prime) (hlt : u<p) :
    u*p ≠ ArithmeticFunction.sigma 2 u := by
  intro eqn
  have hu0 : u≠0 := by rintro rfl; simp at hu
  by_cases hu1 : u=1
  · subst u; simp at eqn; exact hp.ne_one eqn
  have podd : Odd p := hp.eq_two_or_odd'.resolve_left (by omega)
  let S (q:ℕ) := ∑ i ∈ Finset.range (u.factorization q+1), q^(i*2)
  have eqprod : u*p=∏q∈u.primeFactors,S q :=
    eqn.trans (ArithmeticFunction.sigma_eq_prod_primeFactors_sum_range_factorization_pow_mul hu0)
  have pd : p∣∏q∈u.primeFactors,S q := eqprod ▸ dvd_mul_left p u
  obtain ⟨q,hq,hs⟩ := ((Nat.prime_iff.mp hp).dvd_finsetProd_iff S).mp pd
  have qp := Nat.prime_of_mem_primeFactors hq
  have qd := Nat.dvd_of_mem_primeFactors hq
  let a := u.factorization q
  have ha : 0<a := qp.factorization_pos_of_dvd hu0 qd
  have qpow : q^a∣u := (qp.pow_dvd_iff_le_factorization hu0).mpr le_rfl
  have qodd : Odd q := qp.eq_two_or_odd'.resolve_left (by rintro rfl; exact hu.not_two_dvd_nat qd)
  have so : Odd (S q) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact (hu.mul podd).not_two_dvd_nat ((even_iff_two_dvd.mp he).trans
      (eqprod ▸ Finset.dvd_prod_of_mem S hq))
  have ao : Odd (a+1) := by
    have h := (Finset.odd_sum_iff_odd_card_odd (s:=Finset.range (a+1)) (fun i => q^(i*2))).mp so
    simpa [qodd.pow] using h
  obtain ⟨v,hv⟩ := qpow
  by_cases hv1 : v=1
  · have ue : u=q^a := by simpa [hv1] using hv
    have qS : q∣S q := by
      have h := qd.trans (dvd_mul_right u p)
      rw [eqn,ue, ArithmeticFunction.sigma_apply_prime_pow qp] at h
      exact h
    have rest : (S q)%q=1 := by
      unfold S
      rw [Finset.sum_range_succ']
      have hz : q ∣ ∑ i ∈ Finset.range (u.factorization q), q^((i+1)*2) :=
        Finset.dvd_sum (by intro i hi; exact dvd_pow_self _ (by omega))
      simp [Nat.add_mod, Nat.mod_eq_zero_of_dvd hz, Nat.mod_eq_of_lt qp.one_lt]
    exact (by rw [Nat.mod_eq_zero_of_dvd qS] at rest; omega)
  · have hv0 : 0<v := by
      by_contra! h
      rw [show v=0 by omega, mul_zero] at hv
      omega
    have big : 2*q^a < p :=
      (calc 2*q^a ≤ v*q^a := Nat.mul_le_mul_right _ (by omega)
            _ = u := by rw [hv,mul_comm]).trans_lt hlt
    exact odd_local_moment hp qp.two_le ha ao big hs

end Div509

namespace Div509
open OMA.S_mo_509919

/-- The native prefix is downward closed among divisors. -/
theorem mem_prefix_of_dvd_le {n k x y : ℕ} (hn : n ≠ 0) (hx : x ∣ n) (hxy : x ≤ y)
    (hy : y ∈ n.divisors.sort.take k) : x ∈ n.divisors.sort.take k := by
  let l := n.divisors.sort
  have hsort : l.Pairwise (· ≤ ·) := Finset.pairwise_sort _ _
  have hmem : x ∈ l := (Finset.mem_sort (· ≤ ·)).mpr (Nat.mem_divisors.mpr ⟨hx,hn⟩)
  rw [← List.take_append_drop k l] at hsort hmem
  rcases List.mem_append.mp hmem with h | h
  · exact h
  · have he := (List.pairwise_append.mp hsort).2.2 y hy x h
    exact (le_antisymm hxy he) ▸ hy

/-- Successive odd complementary divisors differ by at least two. This makes
the squares of proper divisors telescope against u times their successive gaps. -/
theorem odd_divisor_step {u x y : ℕ} (ho : Odd u) (hx : 0 < x) (hxy : x < y) (hyu : y < u)
    (hxd : x ∣ u) (hyd : y ∣ u) : u*x+y^2 ≤ u*y := by
  obtain ⟨i,hi⟩ := hxd
  obtain ⟨j,hj⟩ := hyd
  have hpos : 0 < j := Nat.pos_of_mul_pos_left (hj ▸ (show 0 < u by omega))
  have htwo : 2 ≤ j := by
    by_contra! hh
    have hj1 : j=1 := by omega
    rw [hj1,mul_one] at hj
    omega
  have hoi : Odd i := Nat.odd_mul.mp (hi ▸ ho) |>.2
  have hoj : Odd j := Nat.odd_mul.mp (hj ▸ ho) |>.2
  have hlt : j < i := by
    by_contra! h
    have := Nat.mul_le_mul_left x h
    have := Nat.mul_lt_mul_of_pos_right hxy hpos
    omega
  have hdiff : j+2 ≤ i := by obtain ⟨v,hv⟩ := hoi; obtain ⟨w,hw⟩ := hoj; omega
  have ha := Nat.mul_le_mul_left x hdiff
  have hdelta : j*(y-x)+j*x=j*y := by rw [←mul_add,Nat.sub_add_cancel hxy.le]
  have hbig : 2*x ≤ j*(y-x) := by nlinarith only [ha,hi,hj,hdelta]
  have hb : y ≤ j*(y-x) := by
    have := Nat.mul_le_mul_right (y-x) htwo
    omega
  have hc := Nat.mul_le_mul_left y hb
  rw [←mul_assoc,←hj,Nat.mul_sub_left_distrib] at hc
  nlinarith only [hc,Nat.sub_add_cancel (Nat.mul_le_mul_left u hxy.le)]

theorem odd_proper_sum {u : ℕ} (ho : Odd u) (x : ℕ) (l : List ℕ)
    (hs : (x::l).Pairwise (· > ·))
    (hd : ∀ i ∈ x::l, 0 < i ∧ i < u ∧ i ∣ u) :
    ((x::l).map (fun i => i^2)).sum ≤ u*x := by
  induction l generalizing x with
  | nil =>
    simpa [pow_two] using Nat.mul_le_mul_right x (hd x (by simp)).2.1.le
  | cons y l ih =>
    have hxy := (List.pairwise_cons.mp hs).1 y (by simp)
    have hx := hd x (by simp)
    have hy := hd y (by simp)
    have ht := ih y (List.pairwise_cons.mp hs).2 (fun i hi => hd i (List.mem_cons_of_mem _ hi))
    have hstep := odd_divisor_step ho hy.1 hxy hx.2.1 hy.2.2 hx.2.2
    change x^2 + ((y::l).map _).sum ≤ u*x
    omega

end Div509

namespace Div509
open OMA.S_mo_509919

theorem odd_missing_prime_forces_full {n k p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hpn : p ∣ n) (hw : n=sumSqSmallestDivisors k n)
    (hmiss : p ∉ n.divisors.sort.take k) :
    ∃ u : ℕ, Odd u ∧ u < p ∧ u*p=ArithmeticFunction.sigma 2 u := by
  have hpos : 0 < n := by obtain ⟨i,hi⟩ := hn; omega
  obtain ⟨u,hfac⟩ := hpn
  have huo := (Nat.odd_mul.mp (hfac ▸ hn)).2
  have hu : 0 < u := by obtain ⟨i,hi⟩ := huo; omega
  let l := n.divisors.sort.take k
  have hlt {d : ℕ} (hd : d ∈ l) : d < p := by
    by_contra! h
    exact hmiss (mem_prefix_of_dvd_le hpos.ne' (hfac ▸ dvd_mul_right p u) h hd)
  have hdpos {d : ℕ} (hd : d ∈ l) : 0 < d := Nat.pos_of_dvd_of_pos (dvd_of_mem_prefix hd) hpos
  have hcore {d : ℕ} (hd : d ∈ l) : d ∣ u := by
    have hf := dvd_of_mem_prefix hd
    rw [hfac] at hf
    exact (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (hdpos hd) (hlt hd))).symm.dvd_of_dvd_mul_left hf
  have hmem : u ∈ l := by
    by_contra hnone
    have hs : l.Pairwise (· < ·) := (Finset.sortedLT_sort _).pairwise.take
    have hsr : l.reverse.Pairwise (· > ·) := List.pairwise_reverse.mpr hs
    have hsum : (l.reverse.map (fun x => x^2)).sum = n := by
      rw [List.map_reverse,List.sum_reverse]; exact hw.symm
    rcases he : l.reverse with _ | ⟨x,t⟩
    · rw [he] at hsum; simp at hsum; omega
    · have hmem' {i : ℕ} (hi : i ∈ x::t) : i ∈ l := by rw [←he] at hi; simpa using hi
      rw [he] at hsr hsum
      have hb := odd_proper_sum huo x t hsr (fun i hi => by
        have hm := hmem' hi
        have hd := hcore hm
        exact ⟨hdpos hm,lt_of_le_of_ne (Nat.le_of_dvd hu hd) (by rintro rfl; exact hnone hm),hd⟩)
      rw [hsum] at hb
      have hx := hlt (hmem' (show x ∈ x::t by simp))
      have hh := Nat.mul_lt_mul_of_pos_left hx hu
      rw [Nat.mul_comm u p] at hh
      omega
  have hEq : l.toFinset=u.divisors := by
    ext i
    rw [List.mem_toFinset,Nat.mem_divisors]
    exact ⟨fun hi => ⟨hcore hi,hu.ne'⟩,fun hi => mem_prefix_of_dvd_le hpos.ne'
      (hi.1.trans (hfac ▸ dvd_mul_left u p)) (Nat.le_of_dvd hu hi.1) hmem⟩
  have hnodup : l.Nodup := (Finset.sort_nodup _ _).take
  refine ⟨u,huo,hlt hmem,?_⟩
  rw [mul_comm u p,←hfac,ArithmeticFunction.sigma_apply,←hEq,List.sum_toFinset _ hnodup]
  exact hw

end Div509

namespace Div509
open OMA.S_mo_509919

/-- Every prime factor of an odd solution occurs in the selected prefix. -/
theorem odd_prime_in_prefix {n k p : ℕ} (hn : Odd n) (hp : p.Prime)
    (hpn : p ∣ n) (hw : n=sumSqSmallestDivisors k n) :
    p ∈ n.divisors.sort.take k := by
  by_contra hmiss
  obtain ⟨u,hu,hlt,he⟩ := odd_missing_prime_forces_full hn hp hpn hw hmiss
  exact odd_full_prime_impossible hu hp hlt he

end Div509

namespace Div509
open OMA.S_mo_509919

theorem prime_71171 : Nat.Prime 71171 := by
  apply prime_from_factors 71171 2 [2, 5, 11, 647] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 11), (by norm_num1 : Nat.Prime 647)]

theorem prime_569369 : Nat.Prime 569369 := by
  apply prime_from_factors 569369 3 [2, 2, 2, 71171] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), prime_71171]

theorem prime_3236293397 : Nat.Prime 3236293397 := by
  apply prime_from_factors 3236293397 3 [2, 2, 7, 7, 29, 569369] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 29), prime_569369]

theorem prime_904847 : Nat.Prime 904847 := by
  apply prime_from_factors 904847 5 [2, 487, 929] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 487), (by norm_num1 : Nat.Prime 929)]

theorem prime_5083430447 : Nat.Prime 5083430447 := by
  apply prime_from_factors 5083430447 5 [2, 53, 53, 904847] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 53), prime_904847]

theorem prime_5527 : Nat.Prime 5527 := by
  apply prime_from_factors 5527 5 [2, 3, 3, 307] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 307)]

theorem prime_4618073797 : Nat.Prime 4618073797 := by
  apply prime_from_factors 4618073797 5 [2, 2, 3, 7, 7, 7, 7, 29, 5527] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 29), prime_5527]

theorem prime_1229 : Nat.Prime 1229 := by
  apply prime_from_factors 1229 2 [2, 2, 307] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 307)]

theorem prime_17207 : Nat.Prime 17207 := by
  apply prime_from_factors 17207 5 [2, 7, 1229] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 7), prime_1229]

theorem prime_26153 : Nat.Prime 26153 := by
  apply prime_from_factors 26153 3 [2, 2, 2, 7, 467] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 467)]

theorem prime_5400176053 : Nat.Prime 5400176053 := by
  apply prime_from_factors 5400176053 2 [2, 2, 3, 17207, 26153] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_17207, prime_26153]

theorem prime_2767 : Nat.Prime 2767 := by
  apply prime_from_factors 2767 3 [2, 3, 461] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 461)]

theorem prime_49807 : Nat.Prime 49807 := by
  apply prime_from_factors 49807 3 [2, 3, 3, 2767] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_2767]

theorem prime_8979903259 : Nat.Prime 8979903259 := by
  apply prime_from_factors 8979903259 19 [2, 3, 151, 199, 49807] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 151), (by norm_num1 : Nat.Prime 199), prime_49807]

theorem prime_119557 : Nat.Prime 119557 := by
  apply prime_from_factors 119557 2 [2, 2, 3, 3, 3, 3, 3, 3, 41] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 41)]

theorem prime_2869369 : Nat.Prime 2869369 := by
  apply prime_from_factors 2869369 7 [2, 2, 2, 3, 119557] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_119557]

theorem prime_13956610817 : Nat.Prime 13956610817 := by
  apply prime_from_factors 13956610817 5 [2, 2, 2, 2, 2, 2, 2, 2, 19, 2869369] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 19), prime_2869369]

theorem prime_2081 : Nat.Prime 2081 := by
  apply prime_from_factors 2081 3 [2, 2, 2, 2, 2, 5, 13] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 13)]

theorem prime_2534659 : Nat.Prime 2534659 := by
  apply prime_from_factors 2534659 7 [2, 3, 7, 29, 2081] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 29), prime_2081]

theorem prime_23552051429 : Nat.Prime 23552051429 := by
  apply prime_from_factors 23552051429 2 [2, 2, 23, 101, 2534659] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 23), (by norm_num1 : Nat.Prime 101), prime_2534659]

theorem prime_1319 : Nat.Prime 1319 := by
  apply prime_from_factors 1319 13 [2, 659] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 659)]

theorem prime_40022960429 : Nat.Prime 40022960429 := by
  apply prime_from_factors 40022960429 2 [2, 2, 11, 11, 71, 883, 1319] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 11), (by norm_num1 : Nat.Prime 71), (by norm_num1 : Nat.Prime 883), prime_1319]

theorem prime_89909 : Nat.Prime 89909 := by
  apply prime_from_factors 89909 2 [2, 2, 7, 13, 13, 19] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 13), (by norm_num1 : Nat.Prime 19)]

theorem prime_82716281 : Nat.Prime 82716281 := by
  apply prime_from_factors 82716281 11 [2, 2, 2, 5, 23, 89909] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 23), prime_89909]

theorem prime_85859499679 : Nat.Prime 85859499679 := by
  apply prime_from_factors 85859499679 6 [2, 3, 173, 82716281] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 173), prime_82716281]

theorem prime_42043 : Nat.Prime 42043 := by
  apply prime_from_factors 42043 5 [2, 3, 7, 7, 11, 13] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 11), (by norm_num1 : Nat.Prime 13)]

theorem prime_143881909009 : Nat.Prime 143881909009 := by
  apply prime_from_factors 143881909009 7 [2, 2, 2, 2, 3, 83, 859, 42043] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 83), (by norm_num1 : Nat.Prime 859), prime_42043]

theorem prime_1459 : Nat.Prime 1459 := by
  apply prime_from_factors 1459 3 [2, 3, 3, 3, 3, 3, 3] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3)]

theorem prime_26263 : Nat.Prime 26263 := by
  apply prime_from_factors 26263 3 [2, 3, 3, 1459] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_1459]

theorem prime_550369 : Nat.Prime 550369 := by
  apply prime_from_factors 550369 11 [2, 2, 2, 2, 2, 3, 3, 3, 7, 7, 13] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 13)]

theorem prime_144543410471 : Nat.Prime 144543410471 := by
  apply prime_from_factors 144543410471 11 [2, 5, 26263, 550369] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), prime_26263, prime_550369]

theorem prime_1063 : Nat.Prime 1063 := by
  apply prime_from_factors 1063 3 [2, 3, 3, 59] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 59)]

theorem prime_7691 : Nat.Prime 7691 := by
  apply prime_from_factors 7691 2 [2, 5, 769] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 769)]

theorem prime_1814968327 : Nat.Prime 1814968327 := by
  apply prime_from_factors 1814968327 5 [2, 3, 37, 1063, 7691] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 37), prime_1063, prime_7691]

theorem prime_192386642663 : Nat.Prime 192386642663 := by
  apply prime_from_factors 192386642663 5 [2, 53, 1814968327] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 53), prime_1814968327]

theorem prime_1451 : Nat.Prime 1451 := by
  apply prime_from_factors 1451 2 [2, 5, 5, 29] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 29)]

theorem prime_8707 : Nat.Prime 8707 := by
  apply prime_from_factors 8707 5 [2, 3, 1451] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_1451]

theorem prime_18679 : Nat.Prime 18679 := by
  apply prime_from_factors 18679 6 [2, 3, 11, 283] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 11), (by norm_num1 : Nat.Prime 283)]

theorem prime_224149 : Nat.Prime 224149 := by
  apply prime_from_factors 224149 2 [2, 2, 3, 18679] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_18679]

theorem prime_1014865978361 : Nat.Prime 1014865978361 := by
  apply prime_from_factors 1014865978361 6 [2, 2, 2, 5, 13, 8707, 224149] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 13), prime_8707, prime_224149]

theorem prime_2137 : Nat.Prime 2137 := by
  apply prime_from_factors 2137 10 [2, 2, 2, 3, 89] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 89)]

theorem prime_12823 : Nat.Prime 12823 := by
  apply prime_from_factors 12823 3 [2, 3, 2137] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_2137]

theorem prime_26681 : Nat.Prime 26681 := by
  apply prime_from_factors 26681 6 [2, 2, 2, 5, 23, 29] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 23), (by norm_num1 : Nat.Prime 29)]

theorem prime_160087 : Nat.Prime 160087 := by
  apply prime_from_factors 160087 3 [2, 3, 26681] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_26681]

theorem prime_14087657 : Nat.Prime 14087657 := by
  apply prime_from_factors 14087657 3 [2, 2, 2, 11, 160087] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 11), prime_160087]

theorem prime_361292051423 : Nat.Prime 361292051423 := by
  apply prime_from_factors 361292051423 5 [2, 12823, 14087657] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), prime_12823, prime_14087657]

theorem prime_2167752308539 : Nat.Prime 2167752308539 := by
  apply prime_from_factors 2167752308539 2 [2, 3, 361292051423] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), prime_361292051423]

theorem prime_5953 : Nat.Prime 5953 := by
  apply prime_from_factors 5953 7 [2, 2, 2, 2, 2, 2, 3, 31] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 31)]

theorem prime_680917 : Nat.Prime 680917 := by
  apply prime_from_factors 680917 5 [2, 2, 3, 179, 317] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 179), (by norm_num1 : Nat.Prime 317)]

theorem prime_62577916033639 : Nat.Prime 62577916033639 := by
  apply prime_from_factors 62577916033639 3 [2, 3, 31, 83, 5953, 680917] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 31), (by norm_num1 : Nat.Prime 83), prime_5953, prime_680917]

theorem prime_1327 : Nat.Prime 1327 := by
  apply prime_from_factors 1327 3 [2, 3, 13, 17] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 13), (by norm_num1 : Nat.Prime 17)]

theorem prime_371561 : Nat.Prime 371561 := by
  apply prime_from_factors 371561 3 [2, 2, 2, 5, 7, 1327] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 7), prime_1327]

theorem prime_743123 : Nat.Prime 743123 := by
  apply prime_from_factors 743123 2 [2, 371561] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), prime_371561]

theorem prime_150074660368639 : Nat.Prime 150074660368639 := by
  apply prime_from_factors 150074660368639 3 [2, 3, 3, 3, 3, 43, 53, 547, 743123] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 43), (by norm_num1 : Nat.Prime 53), (by norm_num1 : Nat.Prime 547), prime_743123]

theorem prime_104789 : Nat.Prime 104789 := by
  apply prime_from_factors 104789 2 [2, 2, 17, 23, 67] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 17), (by norm_num1 : Nat.Prime 23), (by norm_num1 : Nat.Prime 67)]

theorem prime_3255127 : Nat.Prime 3255127 := by
  apply prime_from_factors 3255127 5 [2, 3, 7, 17, 47, 97] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 17), (by norm_num1 : Nat.Prime 47), (by norm_num1 : Nat.Prime 97)]

theorem prime_368389623459241 : Nat.Prime 368389623459241 := by
  apply prime_from_factors 368389623459241 7 [2, 2, 2, 3, 3, 3, 5, 104789, 3255127] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 5), prime_104789, prime_3255127]

theorem prime_8647 : Nat.Prime 8647 := by
  apply prime_from_factors 8647 3 [2, 3, 11, 131] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 11), (by norm_num1 : Nat.Prime 131)]

theorem prime_2111 : Nat.Prime 2111 := by
  apply prime_from_factors 2111 7 [2, 5, 211] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 211)]

theorem prime_11383 : Nat.Prime 11383 := by
  apply prime_from_factors 11383 5 [2, 3, 7, 271] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 3), (by norm_num1 : Nat.Prime 7), (by norm_num1 : Nat.Prime 271)]

theorem prime_2066538119 : Nat.Prime 2066538119 := by
  apply prime_from_factors 2066538119 7 [2, 43, 2111, 11383] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 43), prime_2111, prime_11383]

theorem prime_4133076239 : Nat.Prime 4133076239 := by
  apply prime_from_factors 4133076239 13 [2, 2066538119] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), prime_2066538119]

theorem prime_3931258126249631 : Nat.Prime 3931258126249631 := by
  apply prime_from_factors 3931258126249631 11 [2, 5, 11, 8647, 4133076239] (by decide) ?_ (by decide +kernel) (by decide +kernel)
  simp [List.forall_mem_cons, (by norm_num1 : Nat.Prime 2), (by norm_num1 : Nat.Prime 5), (by norm_num1 : Nat.Prime 11), prime_8647, prime_4133076239]

theorem moment_12436023600 (e : ℕ) : ArithmeticFunction.sigma e 12436023600 = (∑ j ∈ Finset.range (4+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 11^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 29^(j*e))))))))) := by
  conv_lhs => rw [show 12436023600 = ((2^4)*((3^2)*((5^2)*((7^2)*((11^1)*((13^1)*((17^1)*(29^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^4) : ℕ).Coprime ((3^2)*((5^2)*((7^2)*((11^1)*((13^1)*((17^1)*(29^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^2)*((7^2)*((11^1)*((13^1)*((17^1)*(29^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^2) : ℕ).Coprime ((7^2)*((11^1)*((13^1)*((17^1)*(29^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((11^1)*((13^1)*((17^1)*(29^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((11^1) : ℕ).Coprime ((13^1)*((17^1)*(29^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((17^1)*(29^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime (29^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 11 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 29 1 (by norm_num1))]

theorem verified_40246621061616169200 : 2157 ≤ (Nat.divisors 40246621061616169200).card ∧ 40246621061616169200=sumSqSmallestDivisors 2157 40246621061616169200 := by
  exact solution_from_complements (u:=12436023600) (p:=3236293397) (r:=4) (k:=2157) (by decide) prime_3236293397 (by decide) (by decide)
    (by rw [moment_12436023600]; decide +kernel) (by rw [moment_12436023600]; decide +kernel)

theorem moment_8147739600 (e : ℕ) : ArithmeticFunction.sigma e 8147739600 = (∑ j ∈ Finset.range (4+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 11^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 19^(j*e))))))))) := by
  conv_lhs => rw [show 8147739600 = ((2^4)*((3^2)*((5^2)*((7^2)*((11^1)*((13^1)*((17^1)*(19^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^4) : ℕ).Coprime ((3^2)*((5^2)*((7^2)*((11^1)*((13^1)*((17^1)*(19^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^2)*((7^2)*((11^1)*((13^1)*((17^1)*(19^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^2) : ℕ).Coprime ((7^2)*((11^1)*((13^1)*((17^1)*(19^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((11^1)*((13^1)*((17^1)*(19^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((11^1) : ℕ).Coprime ((13^1)*((17^1)*(19^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((17^1)*(19^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime (19^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 11 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 19 1 (by norm_num1))]

theorem verified_41418467556867601200 : 2159 ≤ (Nat.divisors 41418467556867601200).card ∧ 41418467556867601200=sumSqSmallestDivisors 2159 41418467556867601200 := by
  exact solution_from_complements (u:=8147739600) (p:=5083430447) (r:=2) (k:=2159) (by decide) prime_5083430447 (by decide) (by decide)
    (by rw [moment_8147739600]; decide +kernel) (by rw [moment_8147739600]; decide +kernel)

theorem verified_57430474726033609200 : 2158 ≤ (Nat.divisors 57430474726033609200).card ∧ 57430474726033609200=sumSqSmallestDivisors 2158 57430474726033609200 := by
  exact solution_from_complements (u:=12436023600) (p:=4618073797) (r:=3) (k:=2158) (by decide) prime_4618073797 (by decide) (by decide)
    (by rw [moment_12436023600]; decide +kernel) (by rw [moment_12436023600]; decide +kernel)

theorem moment_21480404400 (e : ℕ) : ArithmeticFunction.sigma e 21480404400 = (∑ j ∈ Finset.range (4+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 19^(j*e))*((∑ j ∈ Finset.range (1+1), 29^(j*e))))))))) := by
  conv_lhs => rw [show 21480404400 = ((2^4)*((3^2)*((5^2)*((7^2)*((13^1)*((17^1)*((19^1)*(29^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^4) : ℕ).Coprime ((3^2)*((5^2)*((7^2)*((13^1)*((17^1)*((19^1)*(29^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^2)*((7^2)*((13^1)*((17^1)*((19^1)*(29^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^2) : ℕ).Coprime ((7^2)*((13^1)*((17^1)*((19^1)*(29^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((13^1)*((17^1)*((19^1)*(29^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((17^1)*((19^1)*(29^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime ((19^1)*(29^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((19^1) : ℕ).Coprime (29^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 19 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 29 1 (by norm_num1))]

theorem verified_115997965449635833200 : 2157 ≤ (Nat.divisors 115997965449635833200).card ∧ 115997965449635833200=sumSqSmallestDivisors 2157 115997965449635833200 := by
  exact solution_from_complements (u:=21480404400) (p:=5400176053) (r:=4) (k:=2157) (by decide) prime_5400176053 (by decide) (by decide)
    (by rw [moment_21480404400]; decide +kernel) (by rw [moment_21480404400]; decide +kernel)

theorem moment_25559301600 (e : ℕ) : ArithmeticFunction.sigma e 25559301600 = (∑ j ∈ Finset.range (5+1), 2^(j*e))*((∑ j ∈ Finset.range (3+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 19^(j*e))*((∑ j ∈ Finset.range (1+1), 31^(j*e))*((∑ j ∈ Finset.range (1+1), 41^(j*e)))))))) := by
  conv_lhs => rw [show 25559301600 = ((2^5)*((3^3)*((5^2)*((7^2)*((19^1)*((31^1)*(41^1))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^5) : ℕ).Coprime ((3^3)*((5^2)*((7^2)*((19^1)*((31^1)*(41^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^3) : ℕ).Coprime ((5^2)*((7^2)*((19^1)*((31^1)*(41^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^2) : ℕ).Coprime ((7^2)*((19^1)*((31^1)*(41^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((19^1)*((31^1)*(41^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((19^1) : ℕ).Coprime ((31^1)*(41^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((31^1) : ℕ).Coprime (41^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 5 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 19 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 31 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 41 1 (by norm_num1))]

theorem verified_229520055735603914400 : 1726 ≤ (Nat.divisors 229520055735603914400).card ∧ 229520055735603914400=sumSqSmallestDivisors 1726 229520055735603914400 := by
  exact solution_from_complements (u:=25559301600) (p:=8979903259) (r:=3) (k:=1726) (by decide) prime_8979903259 (by decide) (by decide)
    (by rw [moment_25559301600]; decide +kernel) (by rw [moment_25559301600]; decide +kernel)

theorem moment_41533865100 (e : ℕ) : ArithmeticFunction.sigma e 41533865100 = (∑ j ∈ Finset.range (2+1), 2^(j*e))*((∑ j ∈ Finset.range (3+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 19^(j*e))*((∑ j ∈ Finset.range (1+1), 31^(j*e))*((∑ j ∈ Finset.range (1+1), 41^(j*e))))))))) := by
  conv_lhs => rw [show 41533865100 = ((2^2)*((3^3)*((5^2)*((7^2)*((13^1)*((19^1)*((31^1)*(41^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^2) : ℕ).Coprime ((3^3)*((5^2)*((7^2)*((13^1)*((19^1)*((31^1)*(41^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^3) : ℕ).Coprime ((5^2)*((7^2)*((13^1)*((19^1)*((31^1)*(41^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^2) : ℕ).Coprime ((7^2)*((13^1)*((19^1)*((31^1)*(41^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((13^1)*((19^1)*((31^1)*(41^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((19^1)*((31^1)*(41^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((19^1) : ℕ).Coprime ((31^1)*(41^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((31^1) : ℕ).Coprime (41^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 19 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 31 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 41 1 (by norm_num1))]

theorem verified_579671990926478786700 : 1726 ≤ (Nat.divisors 579671990926478786700).card ∧ 579671990926478786700=sumSqSmallestDivisors 1726 579671990926478786700 := by
  exact solution_from_complements (u:=41533865100) (p:=13956610817) (r:=3) (k:=1726) (by decide) prime_13956610817 (by decide) (by decide)
    (by rw [moment_41533865100]; decide +kernel) (by rw [moment_41533865100]; decide +kernel)

theorem moment_65883636000 (e : ℕ) : ArithmeticFunction.sigma e 65883636000 = (∑ j ∈ Finset.range (5+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (3+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (3+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))))))) := by
  conv_lhs => rw [show 65883636000 = ((2^5)*((3^2)*((5^3)*((7^2)*((13^3)*(17^1)))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^5) : ℕ).Coprime ((3^2)*((5^3)*((7^2)*((13^3)*(17^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^3)*((7^2)*((13^3)*(17^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^3) : ℕ).Coprime ((7^2)*((13^3)*(17^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((13^3)*(17^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^3) : ℕ).Coprime (17^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 5 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1))]

theorem verified_1551694783401515844000 : 1726 ≤ (Nat.divisors 1551694783401515844000).card ∧ 1551694783401515844000=sumSqSmallestDivisors 1726 1551694783401515844000 := by
  exact solution_from_complements (u:=65883636000) (p:=23552051429) (r:=3) (k:=1726) (by decide) prime_23552051429 (by decide) (by decide)
    (by rw [moment_65883636000]; decide +kernel) (by rw [moment_65883636000]; decide +kernel)

theorem verified_2636858156546639844000 : 1727 ≤ (Nat.divisors 2636858156546639844000).card ∧ 2636858156546639844000=sumSqSmallestDivisors 1727 2636858156546639844000 := by
  exact solution_from_complements (u:=65883636000) (p:=40022960429) (r:=2) (k:=1727) (by decide) prime_40022960429 (by decide) (by decide)
    (by rw [moment_65883636000]; decide +kernel) (by rw [moment_65883636000]; decide +kernel)

theorem moment_250833082500 (e : ℕ) : ArithmeticFunction.sigma e 250833082500 = (∑ j ∈ Finset.range (2+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (4+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 11^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 37^(j*e))*((∑ j ∈ Finset.range (1+1), 43^(j*e))))))))) := by
  conv_lhs => rw [show 250833082500 = ((2^2)*((3^2)*((5^4)*((7^2)*((11^1)*((13^1)*((37^1)*(43^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^2) : ℕ).Coprime ((3^2)*((5^4)*((7^2)*((11^1)*((13^1)*((37^1)*(43^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^4)*((7^2)*((11^1)*((13^1)*((37^1)*(43^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^4) : ℕ).Coprime ((7^2)*((11^1)*((13^1)*((37^1)*(43^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((11^1)*((13^1)*((37^1)*(43^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((11^1) : ℕ).Coprime ((13^1)*((37^1)*(43^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((37^1)*(43^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((37^1) : ℕ).Coprime (43^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 11 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 37 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 43 1 (by norm_num1))]

theorem verified_21536402966391330517500 : 2158 ≤ (Nat.divisors 21536402966391330517500).card ∧ 21536402966391330517500=sumSqSmallestDivisors 2158 21536402966391330517500 := by
  exact solution_from_complements (u:=250833082500) (p:=85859499679) (r:=3) (k:=2158) (by decide) prime_85859499679 (by decide) (by decide)
    (by rw [moment_250833082500]; decide +kernel) (by rw [moment_250833082500]; decide +kernel)

theorem moment_243898340400 (e : ℕ) : ArithmeticFunction.sigma e 243898340400 = (∑ j ∈ Finset.range (4+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 5^(j*e))*((∑ j ∈ Finset.range (1+1), 11^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 29^(j*e))*((∑ j ∈ Finset.range (2+1), 31^(j*e))))))))) := by
  conv_lhs => rw [show 243898340400 = ((2^4)*((3^2)*((5^2)*((11^1)*((13^1)*((17^1)*((29^1)*(31^2)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^4) : ℕ).Coprime ((3^2)*((5^2)*((11^1)*((13^1)*((17^1)*((29^1)*(31^2))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^2)*((11^1)*((13^1)*((17^1)*((29^1)*(31^2)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^2) : ℕ).Coprime ((11^1)*((13^1)*((17^1)*((29^1)*(31^2))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((11^1) : ℕ).Coprime ((13^1)*((17^1)*((29^1)*(31^2)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((17^1)*((29^1)*(31^2))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime ((29^1)*(31^2)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((29^1) : ℕ).Coprime (31^2) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 11 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 29 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 31 2 (by norm_num1))]

theorem verified_35092558820878908663600 : 2159 ≤ (Nat.divisors 35092558820878908663600).card ∧ 35092558820878908663600=sumSqSmallestDivisors 2159 35092558820878908663600 := by
  exact solution_from_complements (u:=243898340400) (p:=143881909009) (r:=2) (k:=2159) (by decide) prime_143881909009 (by decide) (by decide)
    (by rw [moment_243898340400]; decide +kernel) (by rw [moment_243898340400]; decide +kernel)

theorem moment_433257142500 (e : ℕ) : ArithmeticFunction.sigma e 433257142500 = (∑ j ∈ Finset.range (2+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (4+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 19^(j*e))*((∑ j ∈ Finset.range (1+1), 37^(j*e))*((∑ j ∈ Finset.range (1+1), 43^(j*e))))))))) := by
  conv_lhs => rw [show 433257142500 = ((2^2)*((3^2)*((5^4)*((7^2)*((13^1)*((19^1)*((37^1)*(43^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^2) : ℕ).Coprime ((3^2)*((5^4)*((7^2)*((13^1)*((19^1)*((37^1)*(43^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^4)*((7^2)*((13^1)*((19^1)*((37^1)*(43^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^4) : ℕ).Coprime ((7^2)*((13^1)*((19^1)*((37^1)*(43^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((13^1)*((19^1)*((37^1)*(43^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((19^1)*((37^1)*(43^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((19^1) : ℕ).Coprime ((37^1)*(43^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((37^1) : ℕ).Coprime (43^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 19 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 37 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 43 1 (by norm_num1))]

theorem verified_62624464987870039117500 : 2158 ≤ (Nat.divisors 62624464987870039117500).card ∧ 62624464987870039117500=sumSqSmallestDivisors 2158 62624464987870039117500 := by
  exact solution_from_complements (u:=433257142500) (p:=144543410471) (r:=3) (k:=2158) (by decide) prime_144543410471 (by decide) (by decide)
    (by rw [moment_433257142500]; decide +kernel) (by rw [moment_433257142500]; decide +kernel)

theorem moment_377486756712 (e : ℕ) : ArithmeticFunction.sigma e 377486756712 = (∑ j ∈ Finset.range (3+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 31^(j*e))*((∑ j ∈ Finset.range (2+1), 37^(j*e))*((∑ j ∈ Finset.range (1+1), 43^(j*e)))))))) := by
  conv_lhs => rw [show 377486756712 = ((2^3)*((3^2)*((13^2)*((17^1)*((31^1)*((37^2)*(43^1))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^3) : ℕ).Coprime ((3^2)*((13^2)*((17^1)*((31^1)*((37^2)*(43^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((13^2)*((17^1)*((31^1)*((37^2)*(43^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^2) : ℕ).Coprime ((17^1)*((31^1)*((37^2)*(43^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime ((31^1)*((37^2)*(43^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((31^1) : ℕ).Coprime ((37^2)*(43^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((37^2) : ℕ).Coprime (43^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 31 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 37 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 43 1 (by norm_num1))]

theorem verified_72623409773566360804056 : 863 ≤ (Nat.divisors 72623409773566360804056).card ∧ 72623409773566360804056=sumSqSmallestDivisors 863 72623409773566360804056 := by
  exact solution_from_complements (u:=377486756712) (p:=192386642663) (r:=2) (k:=863) (by decide) prime_192386642663 (by decide) (by decide)
    (by rw [moment_377486756712]; decide +kernel) (by rw [moment_377486756712]; decide +kernel)

theorem moment_2985961387500 (e : ℕ) : ArithmeticFunction.sigma e 2985961387500 = (∑ j ∈ Finset.range (2+1), 2^(j*e))*((∑ j ∈ Finset.range (3+1), 3^(j*e))*((∑ j ∈ Finset.range (5+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 19^(j*e))*((∑ j ∈ Finset.range (1+1), 43^(j*e))))))))) := by
  conv_lhs => rw [show 2985961387500 = ((2^2)*((3^3)*((5^5)*((7^2)*((13^1)*((17^1)*((19^1)*(43^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^2) : ℕ).Coprime ((3^3)*((5^5)*((7^2)*((13^1)*((17^1)*((19^1)*(43^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^3) : ℕ).Coprime ((5^5)*((7^2)*((13^1)*((17^1)*((19^1)*(43^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^5) : ℕ).Coprime ((7^2)*((13^1)*((17^1)*((19^1)*(43^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((13^1)*((17^1)*((19^1)*(43^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((17^1)*((19^1)*(43^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime ((19^1)*(43^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((19^1) : ℕ).Coprime (43^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 5 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 19 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 43 1 (by norm_num1))]

theorem verified_3030350624873356535887500 : 3454 ≤ (Nat.divisors 3030350624873356535887500).card ∧ 3030350624873356535887500=sumSqSmallestDivisors 3454 3030350624873356535887500 := by
  exact solution_from_complements (u:=2985961387500) (p:=1014865978361) (r:=3) (k:=3454) (by decide) prime_1014865978361 (by decide) (by decide)
    (by rw [moment_2985961387500]; decide +kernel) (by rw [moment_2985961387500]; decide +kernel)

theorem moment_6443390362500 (e : ℕ) : ArithmeticFunction.sigma e 6443390362500 = (∑ j ∈ Finset.range (2+1), 2^(j*e))*((∑ j ∈ Finset.range (3+1), 3^(j*e))*((∑ j ∈ Finset.range (5+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 41^(j*e))*((∑ j ∈ Finset.range (1+1), 43^(j*e))))))))) := by
  conv_lhs => rw [show 6443390362500 = ((2^2)*((3^3)*((5^5)*((7^2)*((13^1)*((17^1)*((41^1)*(43^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^2) : ℕ).Coprime ((3^3)*((5^5)*((7^2)*((13^1)*((17^1)*((41^1)*(43^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^3) : ℕ).Coprime ((5^5)*((7^2)*((13^1)*((17^1)*((41^1)*(43^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^5) : ℕ).Coprime ((7^2)*((13^1)*((17^1)*((41^1)*(43^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^2) : ℕ).Coprime ((13^1)*((17^1)*((41^1)*(43^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((17^1)*((41^1)*(43^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime ((41^1)*(43^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((41^1) : ℕ).Coprime (43^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 5 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 41 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 43 1 (by norm_num1))]

theorem verified_13967674333127319055387500 : 3454 ≤ (Nat.divisors 13967674333127319055387500).card ∧ 13967674333127319055387500=sumSqSmallestDivisors 3454 13967674333127319055387500 := by
  exact solution_from_complements (u:=6443390362500) (p:=2167752308539) (r:=3) (k:=3454) (by decide) prime_2167752308539 (by decide) (by decide)
    (by rw [moment_6443390362500]; decide +kernel) (by rw [moment_6443390362500]; decide +kernel)

theorem moment_242298676620000 (e : ℕ) : ArithmeticFunction.sigma e 242298676620000 = (∑ j ∈ Finset.range (5+1), 2^(j*e))*((∑ j ∈ Finset.range (3+1), 3^(j*e))*((∑ j ∈ Finset.range (4+1), 5^(j*e))*((∑ j ∈ Finset.range (1+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 11^(j*e))*((∑ j ∈ Finset.range (2+1), 13^(j*e))*((∑ j ∈ Finset.range (2+1), 29^(j*e))*((∑ j ∈ Finset.range (1+1), 41^(j*e))))))))) := by
  conv_lhs => rw [show 242298676620000 = ((2^5)*((3^3)*((5^4)*((7^1)*((11^1)*((13^2)*((29^2)*(41^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^5) : ℕ).Coprime ((3^3)*((5^4)*((7^1)*((11^1)*((13^2)*((29^2)*(41^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^3) : ℕ).Coprime ((5^4)*((7^1)*((11^1)*((13^2)*((29^2)*(41^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^4) : ℕ).Coprime ((7^1)*((11^1)*((13^2)*((29^2)*(41^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^1) : ℕ).Coprime ((11^1)*((13^2)*((29^2)*(41^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((11^1) : ℕ).Coprime ((13^2)*((29^2)*(41^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^2) : ℕ).Coprime ((29^2)*(41^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((29^2) : ℕ).Coprime (41^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 5 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 11 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 29 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 41 1 (by norm_num1))]

theorem verified_15162546240588209102820180000 : 8637 ≤ (Nat.divisors 15162546240588209102820180000).card ∧ 15162546240588209102820180000=sumSqSmallestDivisors 8637 15162546240588209102820180000 := by
  exact solution_from_complements (u:=242298676620000) (p:=62577916033639) (r:=4) (k:=8637) (by decide) prime_62577916033639 (by decide) (by decide)
    (by rw [moment_242298676620000]; decide +kernel) (by rw [moment_242298676620000]; decide +kernel)

theorem verified_36362891601517191050520180000 : 8639 ≤ (Nat.divisors 36362891601517191050520180000).card ∧ 36362891601517191050520180000=sumSqSmallestDivisors 8639 36362891601517191050520180000 := by
  exact solution_from_complements (u:=242298676620000) (p:=150074660368639) (r:=2) (k:=8639) (by decide) prime_150074660368639 (by decide) (by decide)
    (by rw [moment_242298676620000]; decide +kernel) (by rw [moment_242298676620000]; decide +kernel)

theorem moment_1011490762791600 (e : ℕ) : ArithmeticFunction.sigma e 1011490762791600 = (∑ j ∈ Finset.range (4+1), 2^(j*e))*((∑ j ∈ Finset.range (2+1), 3^(j*e))*((∑ j ∈ Finset.range (2+1), 5^(j*e))*((∑ j ∈ Finset.range (4+1), 7^(j*e))*((∑ j ∈ Finset.range (1+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 17^(j*e))*((∑ j ∈ Finset.range (1+1), 19^(j*e))*((∑ j ∈ Finset.range (1+1), 29^(j*e))*((∑ j ∈ Finset.range (2+1), 31^(j*e)))))))))) := by
  conv_lhs => rw [show 1011490762791600 = ((2^4)*((3^2)*((5^2)*((7^4)*((13^1)*((17^1)*((19^1)*((29^1)*(31^2))))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^4) : ℕ).Coprime ((3^2)*((5^2)*((7^4)*((13^1)*((17^1)*((19^1)*((29^1)*(31^2)))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^2) : ℕ).Coprime ((5^2)*((7^4)*((13^1)*((17^1)*((19^1)*((29^1)*(31^2))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^2) : ℕ).Coprime ((7^4)*((13^1)*((17^1)*((19^1)*((29^1)*(31^2)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((7^4) : ℕ).Coprime ((13^1)*((17^1)*((19^1)*((29^1)*(31^2))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^1) : ℕ).Coprime ((17^1)*((19^1)*((29^1)*(31^2)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((17^1) : ℕ).Coprime ((19^1)*((29^1)*(31^2))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((19^1) : ℕ).Coprime ((29^1)*(31^2)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((29^1) : ℕ).Coprime (31^2) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 7 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 17 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 19 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 29 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 31 2 (by norm_num1))]

theorem verified_372622701237297980961977175600 : 10798 ≤ (Nat.divisors 372622701237297980961977175600).card ∧ 372622701237297980961977175600=sumSqSmallestDivisors 10798 372622701237297980961977175600 := by
  exact solution_from_complements (u:=1011490762791600) (p:=368389623459241) (r:=3) (k:=10798) (by decide) prime_368389623459241 (by decide) (by decide)
    (by rw [moment_1011490762791600]; decide +kernel) (by rw [moment_1011490762791600]; decide +kernel)

theorem moment_6828069275820000 (e : ℕ) : ArithmeticFunction.sigma e 6828069275820000 = (∑ j ∈ Finset.range (5+1), 2^(j*e))*((∑ j ∈ Finset.range (3+1), 3^(j*e))*((∑ j ∈ Finset.range (4+1), 5^(j*e))*((∑ j ∈ Finset.range (2+1), 13^(j*e))*((∑ j ∈ Finset.range (1+1), 31^(j*e))*((∑ j ∈ Finset.range (2+1), 37^(j*e))*((∑ j ∈ Finset.range (1+1), 41^(j*e))*((∑ j ∈ Finset.range (1+1), 43^(j*e))))))))) := by
  conv_lhs => rw [show 6828069275820000 = ((2^5)*((3^3)*((5^4)*((13^2)*((31^1)*((37^2)*((41^1)*(43^1)))))))) by decide]
  simp only [ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((2^5) : ℕ).Coprime ((3^3)*((5^4)*((13^2)*((31^1)*((37^2)*((41^1)*(43^1))))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((3^3) : ℕ).Coprime ((5^4)*((13^2)*((31^1)*((37^2)*((41^1)*(43^1)))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((5^4) : ℕ).Coprime ((13^2)*((31^1)*((37^2)*((41^1)*(43^1))))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((13^2) : ℕ).Coprime ((31^1)*((37^2)*((41^1)*(43^1)))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((31^1) : ℕ).Coprime ((37^2)*((41^1)*(43^1))) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((37^2) : ℕ).Coprime ((41^1)*(43^1)) by decide),
    ArithmeticFunction.isMultiplicative_sigma.map_mul_of_coprime (show ((41^1) : ℕ).Coprime (43^1) by decide),
    (@ArithmeticFunction.sigma_apply_prime_pow e 2 5 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 3 3 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 5 4 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 13 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 31 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 37 2 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 41 1 (by norm_num1)),
    (@ArithmeticFunction.sigma_apply_prime_pow e 43 1 (by norm_num1))]

theorem verified_26842902827162808074712222420000 : 8639 ≤ (Nat.divisors 26842902827162808074712222420000).card ∧ 26842902827162808074712222420000=sumSqSmallestDivisors 8639 26842902827162808074712222420000 := by
  exact solution_from_complements (u:=6828069275820000) (p:=3931258126249631) (r:=2) (k:=8639) (by decide) prime_3931258126249631 (by decide) (by decide)
    (by rw [moment_6828069275820000]; decide +kernel) (by rw [moment_6828069275820000]; decide +kernel)

end Div509

namespace OMA.R_mo_509919_R1
open OMA.S_mo_509919
open Div509

/-- With bounded total prime multiplicity, must all but one distinct prime
in a solution belong to a bounded range independent of the prefix length? -/
def H1 : Prop := ∀ R : ℕ, ∃ P : ℕ, ∀ n k : ℕ, n.primeFactorsList.length ≤ R →
    k ≤ n.divisors.card → n=sumSqSmallestDivisors k n →
    ∃ p : ℕ, ∀ q ∈ n.primeFactorsList, q ≠ p → q ≤ P

/-- The case of one exceptional prime, allowing arbitrary prefix length and
repetitions of that prime. An explicit uniform cutoff is proved below. -/
def H2 : Prop := ∀ R P : ℕ, {n : ℕ | n.primeFactorsList.length ≤ R ∧
    (∃ k : ℕ, k ≤ n.divisors.card ∧ n=sumSqSmallestDivisors k n) ∧
    ∃ p : ℕ, ∀ q ∈ n.primeFactorsList, q ≠ p → q ≤ P}.Finite

theorem main : H1 → H2 → type_of% @OMA.S_mo_509919.main := by
  intro h₁ h₂ k
  cases k with
  | zero =>
    apply (Set.finite_singleton 0).subset
    intro n hn
    have hx := hn.2
    simpa [sumSqSmallestDivisors] using hx
  | succ j =>
    obtain ⟨P,hP⟩ := h₁ (2*j)
    apply ((Set.finite_Iic ((j+1)^(2*j+1))).union (h₂ (2*j) P)).subset
    intro n hn
    rcases le_or_gt n.primeFactorsList.length (2*j) with hlow | hhigh
    · exact Or.inr ⟨hlow,⟨j+1,hn⟩,hP n (j+1) hlow hn.1 hn.2⟩
    · exact Or.inl (multiplicity_cutoff hn.2 (by omega))

theorem one_exceptional_prime_finite : H2 := by
  intro R P
  apply (Set.finite_Iic ((P+1+2^R*((P+1)^R)^2)^R)).subset
  rintro n ⟨hr,⟨k,hk,hw⟩,hp⟩
  exact one_large_cutoff hr hk hw hp

theorem second_prime_bound_necessary (h : type_of% @OMA.S_mo_509919.main) : H1 := by
  have upper (k : ℕ) : ∃ B : ℕ, ∀ n : ℕ, k ≤ n.divisors.card ∧ n=sumSqSmallestDivisors k n → n ≤ B := by
    obtain ⟨M,hM⟩ := (h k).bddAbove
    exact ⟨M,fun _ hn => hM hn⟩
  choose B hB using upper
  intro R
  refine ⟨∑ i ∈ Finset.range (2^R+1), B i,?_⟩
  intro n k hr hk hw
  have hsmall := hk.trans ((divisors_at_most_two_pow n).trans (Nat.pow_le_pow_right (by decide) hr))
  refine ⟨0,?_⟩
  intro q hq _
  have hn : n ≠ 0 := by rintro rfl; simp at hq
  exact (Nat.le_of_dvd hn.bot_lt (Nat.dvd_of_mem_primeFactorsList hq)).trans
    ((hB k n ⟨hk,hw⟩).trans (Finset.single_le_sum (fun i _ => Nat.zero_le (B i))
      (Finset.mem_range.mpr (by omega))))

theorem iff_second_prime_bound : (type_of% @OMA.S_mo_509919.main) ↔ H1 :=
  ⟨second_prime_bound_necessary, fun h => main h one_exceptional_prime_finite⟩

end OMA.R_mo_509919_R1
