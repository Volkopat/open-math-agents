import OMAStatements.S_oeis_a120123

/- A positive fixed point with k digits satisfies
   10^k ≤ 10 m ≤ 10 · 9^k · (9k).
   From k = 85 onward the left side grows strictly faster.
   Within the remaining lengths it suffices to inspect digit multisets:
   their product and sum determine the only possible fixed point. -/

namespace DigitFixedPoint

def stats : ℕ → ℕ → ℕ × ℕ
  | 0, _ => (1, 0)
  | k + 1, n =>
    if n = 0 then (1, 0) else
      let t := stats k (n / 10)
      (n % 10 * t.1, n % 10 + t.2)

theorem stats_digits (n k : ℕ) (h : (Nat.digits 10 n).length ≤ k) :
    stats k n = ((Nat.digits 10 n).prod, (Nat.digits 10 n).sum) := by
  induction k generalizing n with
  | zero =>
    have hn : n = 0 := by
      apply (Nat.digits_eq_nil_iff_eq_zero (b := 10)).mp
      apply List.length_eq_zero_iff.mp
      omega
    simp [hn, stats]
  | succ k ih =>
    by_cases hn : n = 0
    · simp [hn, stats]
    · rw [Nat.digits_eq_cons_digits_div (by decide) hn] at h ⊢
      simp only [List.length_cons, Nat.add_le_add_iff_right] at h
      simp [stats, hn, ih _ h]

/-- Euler's product formula is cheaper to evaluate than counting coprime residues. -/
def phi (s : ℕ) : ℕ := (s / ∏ q ∈ s.primeFactors, q) * ∏ q ∈ s.primeFactors, (q - 1)

def test (len low p s : ℕ) : Bool :=
  if p % 9 = 0 && s % 9 != 0 then true else
    let m := p * phi s
    m < low || m % 10 == 0 || m % 9 != s % 9 || stats len m != (p, s)

/-- Read candidate digits in decreasing order. A tail of k digits bounded by d
has product at most d^k and adds at most k*d to the digit sum. -/
def search (len low : ℕ) : ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, p, s => test len low p s
  | k + 1, d, p, s =>
      if p * d^(k+1) * (s + (k+1)*d) < low ∨ p % 10 = 0 then true else
        (List.range (d+1)).all fun v =>
          if v = 0 then true else search len low k v (p*v) (s+v)

/-- Fix the number of nines before searching the other digits. This divides
the finite verification into small, independently checkable cases. -/
def checkBlock (k j : ℕ) : Bool :=
  search k (max 139969 (10^(k-1))) (k-j) 8 (9^j) (j*9)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem checked (k j : ℕ) (hk : k < 85) (hj : j ≤ k) : checkBlock k j = true := by
  interval_cases k <;> interval_cases j <;> decide +kernel

theorem test_hits {len low m p s : ℕ}
    (hlen : (Nat.digits 10 m).length ≤ len) (hlow : low ≤ m)
    (hlast : m % 10 ≠ 0) (hp : p = (Nat.digits 10 m).prod)
    (hs : s = (Nat.digits 10 m).sum) (hm : m = p * s.totient) :
    test len low p s = false := by
  have hmod : m % 9 = s % 9 := hs ▸ Nat.modEq_digits_sum 9 10 (by decide) m
  have hskip : ¬(p % 9 = 0 ∧ s % 9 ≠ 0) := by
    rintro ⟨hd, hne⟩
    apply hne
    rw [← hmod, hm, Nat.mul_mod, hd]
    simp
  have hstat : stats len m = (p,s) := by rw [stats_digits m len hlen, hp, hs]
  have hphi : phi s = s.totient := (Nat.totient_eq_div_primeFactors_mul s).symm
  unfold test
  simp only [bne_iff_ne, Bool.and_eq_true, decide_eq_true_eq, ne_eq] at *
  rw [if_neg hskip, hphi, ← hm]
  simp [Nat.not_lt.mpr hlow, hlast, hmod, hstat]

theorem search_hits {len low m : ℕ}
    (hlen : (Nat.digits 10 m).length ≤ len) (hlow : low ≤ m) (hlast : m % 10 ≠ 0)
    (hm : m = (Nat.digits 10 m).prod * (Nat.digits 10 m).sum.totient)
    (xs : List ℕ) (hd : xs.Pairwise (· ≥ ·)) (d p s : ℕ)
    (bounds : ∀ v ∈ xs, 0 < v ∧ v ≤ d)
    (hp : p * xs.prod = (Nat.digits 10 m).prod)
    (hs : s + xs.sum = (Nat.digits 10 m).sum) :
    search len low xs.length d p s = false := by
  induction xs generalizing d p s with
  | nil =>
    simp only [List.prod_nil, mul_one] at hp
    simp only [List.sum_nil, add_zero] at hs
    exact test_hits hlen hlow hlast hp hs (by simpa [hp, hs] using hm)
  | cons v vs ih =>
    have hpos := (bounds v (by simp)).1
    have hv := (bounds v (by simp)).2
    have top : ∀ x ∈ v :: vs, x ≤ d := fun x hx => (bounds x hx).2
    have hprod := List.prod_le_pow_card _ _ top
    have hsum := List.sum_le_card_nsmul _ _ top
    simp only [nsmul_eq_mul, List.length_cons] at hsum
    simp only [List.length_cons] at hprod
    have bound : low ≤ p * d ^ (vs.length + 1) * (s + (vs.length + 1) * d) := by
      calc
        low ≤ m := hlow
        _ = _ := hm
        _ ≤ _ := Nat.mul_le_mul (Nat.le_of_eq hp.symm) (Nat.totient_le _)
        _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left p hprod) (hs ▸ Nat.add_le_add_left hsum s)
    have hp10 : p % 10 ≠ 0 := by
      intro hx
      apply hlast
      rw [hm, ← hp, mul_assoc, Nat.mul_mod, hx]
      simp
    simp only [List.length_cons, search, Nat.not_lt.mpr bound, hp10, or_self, if_false]
    apply Bool.eq_false_iff.mpr
    intro hall
    have hh := List.all_eq_true.mp hall v (List.mem_range.mpr (by omega))
    have hit := ih (List.pairwise_cons.mp hd).2 v (p*v) (s+v)
      (fun x hx => ⟨(bounds x (by simp [hx])).1, (List.pairwise_cons.mp hd).1 _ hx⟩)
      (by simpa [List.prod_cons, Nat.mul_assoc] using hp)
      (by simpa [List.sum_cons, Nat.add_assoc] using hs)
    simp [Nat.ne_of_gt hpos, hit] at hh

theorem cutoff (k : ℕ) (hk : 85 ≤ k) : 10 * (9 ^ k * (9 * k)) < 10 ^ k := by
  induction k, hk using Nat.le_induction with
  | base => decide
  | succ k hk ih =>
    have h : 9 * (k+1) ≤ 10*k := by omega
    calc
      10 * (9 ^ (k+1) * (9 * (k+1))) ≤ 10 * (9 ^ (k+1) * (10*k)) := by gcongr
      _ = (10 * (9 ^ k * (9 * k))) * 10 := by rw [pow_succ]; ring
      _ < 10^(k+1) := by rw [pow_succ]; omega

theorem fixed_length {m : ℕ} (hm : 0 < m)
    (h : m = (Nat.digits 10 m).prod * (Nat.digits 10 m).sum.totient) :
    (Nat.digits 10 m).length < 85 := by
  let ds := Nat.digits 10 m
  have hb : ∀ d ∈ ds, d ≤ 9 := fun d hd => by
    have := Nat.digits_lt_base (by decide : 1 < 10) hd
    omega
  have hp := List.prod_le_pow_card _ _ hb
  have hs := List.sum_le_card_nsmul _ _ hb
  simp only [nsmul_eq_mul] at hs
  have hu : m ≤ 9^ds.length * (9*ds.length) :=
    h.trans_le (Nat.mul_le_mul hp ((Nat.totient_le ds.sum).trans (by simpa [Nat.mul_comm] using hs)))
  by_contra! hlarge
  have hc := cutoff ds.length hlarge
  have hl := Nat.base_pow_length_digits_le 10 m (by decide) hm.ne'
  change 10 ^ ds.length ≤ 10 * m at hl
  omega

end DigitFixedPoint

open DigitFixedPoint

theorem OMA.solution : type_of% @OMA.S_oeis_a120123.main := by
  constructor
  · constructor
    · decide
    · change 139968 = (Nat.digits 10 139968).prod * (Nat.digits 10 139968).sum.totient
      decide +kernel
  · intro m hm
    obtain ⟨hm, hfix⟩ := hm
    change m = (Nat.digits 10 m).prod * (Nat.digits 10 m).sum.totient at hfix
    by_contra! hbig
    let ds := Nat.digits 10 m
    have hlen : ds.length < 85 := fixed_length hm hfix
    have hz : 0 ∉ ds := by
      intro h0
      have hp := List.prod_eq_zero h0
      change m = ds.prod * _ at hfix
      rw [hp, zero_mul] at hfix
      omega
    have last : m % 10 ≠ 0 := by
      intro h
      apply hz
      change 0 ∈ Nat.digits 10 m
      rw [Nat.digits_eq_cons_digits_div (by decide) hm.ne', h]
      simp
    have hpos : 0 < ds.length :=
      List.length_pos_iff.mpr (Nat.digits_ne_nil_iff_ne_zero.mpr hm.ne')
    have hlow : max 139969 (10^(ds.length-1)) ≤ m :=
      max_le (by omega) ((Nat.lt_digits_length_iff (by decide) m).mp (by change _ < ds.length; omega))
    let nines := ds.filter (· == 9)
    let small := ds.filter (fun d => !(d == 9))
    let ordered := small.mergeSort (· ≥ ·)
    let j := nines.length
    have part : (nines ++ small).Perm ds := List.filter_append_perm _ _
    have rep : nines = List.replicate j 9 := List.eq_replicate_of_mem (by
      intro v hv; exact beq_iff_eq.mp (List.mem_filter.mp hv).2)
    have perm : ordered.Perm small := List.mergeSort_perm _ _
    have sorted : ordered.Pairwise (· ≥ ·) := List.pairwise_mergeSort' (· ≥ ·) small
    have bounds : ∀ v ∈ ordered, 0 < v ∧ v ≤ 8 := by
      intro v hv
      obtain ⟨hd, hnine⟩ := List.mem_filter.mp (perm.mem_iff.mp hv)
      simp at hnine
      have hu := Nat.digits_lt_base (by decide : 1 < 10) hd
      have hn : v ≠ 0 := by rintro rfl; exact hz hd
      omega
    have hp := part.prod_eq
    have hs := part.sum_eq
    rw [List.prod_append, rep, List.prod_replicate, ← perm.prod_eq] at hp
    rw [List.sum_append, rep, List.sum_replicate, nsmul_eq_mul, ← perm.sum_eq] at hs
    have hit := search_hits (len := ds.length) (Nat.le_refl _) hlow last hfix ordered sorted 8 _ _ bounds hp hs
    have hl : j + ordered.length = ds.length := by simpa [j, perm.length_eq] using part.length_eq
    rw [show ordered.length = ds.length-j by omega] at hit
    change checkBlock ds.length j = false at hit
    have certified := checked ds.length j hlen (by omega)
    simp [certified] at hit
