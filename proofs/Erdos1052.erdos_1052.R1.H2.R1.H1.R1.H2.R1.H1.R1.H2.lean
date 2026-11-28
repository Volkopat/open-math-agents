import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1.H2

Hypothesis H2 of reduction `Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H1.R1` (unitary perfect numbers
`n = 2 ^ a * 5 ^ 2 * (simple odd primes)` with `a = 2 mod 4`): then `a ≤ 63`. Of the hypotheses of the step only
`a = 2 mod 4` is used.

Credit: @aroth01. The base lemmas (`facts`, `path_bound`, `tail_bound`, `exists_child`, `kernel_balance_one`, ...)
are those of reductions `...R1.H2.R1.H1.R1` and `...R1.H2.R1.H1.R1.H2.R1`.

Setting. `P` is the set of simple odd primes (5 is not one of them). `13 ∣ 1 + 5 ^ 2` is a simple prime that
divides no `p + 1`, and `7` divides only `13 + 1`. Every simple prime `p` has `p + 1 = 2 ^ i * 5 ^ j * d` with `d` a
product of distinct simple primes, each dividing only this `p + 1`. Ledger: `5 ∣ 2 ^ a + 1`, so `5 ^ 2` does not
divide the product of the `p + 1`. Balance: the product of the `1 + 1 / p` times `(1 + 1 / 2 ^ a) * (26 / 25)` is `2`.

Proof. A search tree over statements `St P X Y N`: the members of the list `X` are simple primes, those of `Y`
are not, and every simple prime below `N` is in `X`.
* `extend` moves `N` to `N' < 2 * N`: a simple prime `p < N'` outside `X` has all the odd prime factors of `p + 1`
  below `N`, hence in `X` and open (dividing no `x + 1` with `x` in `X`), so `p` is one of finitely many
  numbers `2 ^ i * 5 ^ j * d - 1`; the computable check `winOk` finds a proper factor of each of them.
* `up_kill`: the weight of `X` alone is at least `2`.
* `low_kill`: the unknown simple primes are at least `N` and lie on disjoint paths (`path_bound`) that start at a
  parent of an open member of `X`, at a prime `q` with `5 ∣ q + 1` (the ledger bounds their number) or at a
  Mersenne prime (`tail_bound`); so their weight is at most
  `((N + 1) / (N - 1)) ^ (opens + ledger) * (N + 1) / (N - 3)`, which is too small.
The tree is a term of the type `T` (Section 7); `sound` reduces the step to one evaluation of the checker `chk`,
which the kernel performs (`decide +kernel`). The tree was found by an exact search; nothing about the search is
trusted.
-/

namespace OMA.P_Erdos1052_z5_e2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts path_bound tail_bound exists_child two_mul_le B_step B_anti
  B_nonneg one_add_le_B kernel_balance_one two_pow_of_no_odd_prime five_dvd_two_pow_add_one prime_dvd_prime_pow)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

-- Section 1. The checks, as computable functions on lists of numbers.

/-- The products of the sublists of a list. -/
def subProds : List ℕ → List ℕ
  | [] => [1]
  | c :: t => subProds t ++ (subProds t).map (fun d => c * d)

/-- The open members of `X`: not closed, and dividing no `x + 1` with `x` in `X`. -/
def opens (X : List ℕ) : List ℕ :=
  X.filter (fun c => c != 13 && X.all (fun x => (x + 1) % c != 0))

/-- The product of the `x + 1`. -/
def succProd (X : List ℕ) : ℕ := (X.map (fun x => x + 1)).prod

/-- A candidate `v` is harmless: above the window, known, excluded, or with a proper factor in `F`. -/
def candOk (X Y F : List ℕ) (N' v : ℕ) : Bool :=
  decide (N' ≤ v) || decide (v ∈ X) || decide (v ∈ Y) ||
    F.any (fun f => decide (1 < f) && decide (f < v) && v % f == 0)

/-- The window check: for `d` a product of distinct open members of `X` and `5 ^ j` allowed by the ledger, the
only number `2 ^ i * 5 ^ j * d - 1` in `[N, 2 * N)` is harmless. -/
def winOk (X Y F : List ℕ) (N N' : ℕ) : Bool :=
  decide (N' < 2 * N) &&
    (subProds (opens X)).all (fun d => (List.range 2).all (fun j =>
      (5 ^ j * succProd X) % 5 ^ 2 == 0 || decide (N < 5 ^ j * d) ||
        candOk X Y F N' (2 ^ (Nat.log2 (N / (5 ^ j * d)) + 1) * (5 ^ j * d) - 1)))

/-- The weight of `X` alone is already too large. -/
def upOk (X : List ℕ) : Bool := decide (2 * 25 * X.prod ≤ 26 * succProd X)

/-- How many more simple primes `q` can have `5 ∣ q + 1`. -/
def ledgerLeft (X : List ℕ) : ℕ :=
  if (5 ^ 1 * succProd X) % 5 ^ 2 == 0 then 0 else 1

/-- The weight of `X` together with everything that can still come above `N` is too small. -/
def lowOk (X : List ℕ) (N : ℕ) : Bool :=
  decide (5 ≤ N) &&
    decide ((2 ^ 64 + 1) * 26 * succProd X * (N + 1) ^ ((opens X).length + ledgerLeft X + 1) <
      2 * 2 ^ 64 * 25 * X.prod * (N - 1) ^ ((opens X).length + ledgerLeft X) * (N - 3))

-- Section 2. The setting and the state of the search.

/-- What is known about the set `P` of simple odd primes. -/
structure Ctx (P : Finset ℕ) (m : ℕ) : Prop where
  hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2
  E : (2 ^ m + 1) * 26 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 25 * ∏ p ∈ P, p
  s1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P
  s3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p'
  s6 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 5 → ∀ p ∈ P, ¬ c * c ∣ p + 1
  hc13 : ∀ p ∈ P, ¬ 13 ∣ p + 1
  led : ¬ 5 ^ 2 ∣ ∏ p ∈ P, (p + 1)
  hm : 64 ≤ m

/-- The state: the members of `X` are simple primes, those of `Y` are not, and every simple prime below `N` is
in `X`. -/
def St (P : Finset ℕ) (X Y : List ℕ) (N : ℕ) : Prop :=
  (∀ x ∈ X, x ∈ P) ∧ X.Nodup ∧ (∀ y ∈ Y, y ∉ P) ∧ ∀ p ∈ P, p < N → p ∈ X

theorem incl {P : Finset ℕ} {X Y : List ℕ} {N y : ℕ} (h : St P X Y N) (hy : y ∈ P) (hyX : y ∉ X) :
    St P (y :: X) Y N := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
  refine ⟨fun x hx => ?_, List.nodup_cons.mpr ⟨hyX, hXn⟩, hY, fun p hp hpN => List.mem_cons_of_mem _ (hcl p hp hpN)⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hy
  · exact hXP x hx

theorem excl {P : Finset ℕ} {X Y : List ℕ} {N y : ℕ} (h : St P X Y N) (hy : y ∉ P) : St P X (y :: Y) N := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
  refine ⟨hXP, hXn, fun x hx => ?_, hcl⟩
  rcases List.mem_cons.mp hx with rfl | hx
  · exact hy
  · exact hY x hx

-- Section 3. Elementary lemmas.

theorem mem_subProds : ∀ (l : List ℕ), (∀ c ∈ l, c.Prime) → ∀ d : ℕ, d ∣ l.prod → d ∈ subProds l
  | [], _, d, hd => by
    rw [List.prod_nil, Nat.dvd_one] at hd
    rw [hd]
    exact List.mem_singleton.mpr rfl
  | c :: t, hl, d, hd => by
    have hc : c.Prime := hl c List.mem_cons_self
    have ht : ∀ x ∈ t, x.Prime := fun x hx => hl x (List.mem_cons_of_mem _ hx)
    rw [List.prod_cons] at hd
    unfold subProds
    rw [List.mem_append, List.mem_map]
    by_cases hcd : c ∣ d
    · obtain ⟨d', rfl⟩ := hcd
      exact Or.inr ⟨d', mem_subProds t ht d' (Nat.dvd_of_mul_dvd_mul_left hc.pos hd), rfl⟩
    · have hcop : Nat.Coprime d c := ((Nat.Prime.coprime_iff_not_dvd hc).mpr hcd).symm
      rw [mul_comm] at hd
      exact Or.inl (mem_subProds t ht d (Nat.Coprime.dvd_of_dvd_mul_right hcop hd))

theorem dvd_of_primes {d D : ℕ} (hsq : ∀ c : ℕ, c.Prime → ¬ c * c ∣ d)
    (h : ∀ c : ℕ, c.Prime → c ∣ d → c ∣ D) : d ∣ D := by
  refine (Nat.dvd_iff_prime_pow_dvd_dvd D d).mpr fun c k hc hck => ?_
  rcases k with _ | _ | k
  · rw [pow_zero]
    exact one_dvd _
  · rw [zero_add, pow_one] at hck ⊢
    exact h c hc hck
  · exact absurd ((Dvd.intro (c ^ k) (by ring) : c * c ∣ c ^ (k + 1 + 1)).trans hck) (hsq c hc)

theorem mem_opens {X : List ℕ} {c : ℕ} (hc : c ∈ X) (h13 : c ≠ 13)
    (h : ∀ x ∈ X, ¬ c ∣ x + 1) : c ∈ opens X := by
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨h13, fun x hx hmod => h x hx (Nat.dvd_of_mod_eq_zero hmod)⟩

theorem succProd_eq {X : List ℕ} (hn : X.Nodup) : ∏ x ∈ X.toFinset, (x + 1) = succProd X :=
  List.prod_toFinset _ hn

theorem prod_eq {X : List ℕ} (hn : X.Nodup) : ∏ x ∈ X.toFinset, x = X.prod := by
  rw [List.prod_toFinset _ hn, List.map_id']

/-- The ledger: a set `T` of simple primes outside `X` contributes its `q + 1` next to those of `X`. -/
theorem prod_mul_dvd {P : Finset ℕ} {X : List ℕ} (hXP : ∀ x ∈ X, x ∈ P) (hn : X.Nodup)
    {T : Finset ℕ} (hT : T ⊆ P) (hTX : ∀ q ∈ T, q ∉ X) :
    (∏ q ∈ T, (q + 1)) * succProd X ∣ ∏ p ∈ P, (p + 1) := by
  have hdisj : Disjoint T X.toFinset :=
    Finset.disjoint_left.mpr fun q hq hqX => hTX q hq (List.mem_toFinset.mp hqX)
  rw [← succProd_eq hn, ← Finset.prod_union hdisj]
  exact Finset.prod_dvd_prod_of_subset _ _ _
    (Finset.union_subset hT fun x hx => hXP x (List.mem_toFinset.mp hx))

theorem pow_mul_dvd {a b s : ℕ} (hab : a ≤ b) (h : 5 ^ 2 ∣ 5 ^ a * s) : 5 ^ 2 ∣ 5 ^ b * s :=
  h.trans (Nat.mul_dvd_mul_right (pow_dvd_pow 5 hab) s)

/-- The only `2 ^ i * w` in `(N, 2 * N)` is the one given by the binary logarithm of `N / w`. -/
theorem pow_window {N w i t : ℕ} (hw : 0 < w) (hwN : w ≤ N) (ht : t = 2 ^ i * w) (h1 : N < t) (h2 : t < 2 * N) :
    2 ^ (Nat.log2 (N / w) + 1) * w = t := by
  have hq0 : N / w ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.div_pos hwN hw)
  have hk1 : 2 ^ Nat.log2 (N / w) * w ≤ N :=
    (Nat.mul_le_mul_right _ (Nat.log2_self_le hq0)).trans (Nat.div_mul_le_self _ _)
  have hk2 : N < 2 ^ (Nat.log2 (N / w) + 1) * w := (Nat.div_lt_iff_lt_mul hw).mp Nat.lt_log2_self
  have hgt : Nat.log2 (N / w) < i := by
    by_contra hle
    have h3 := Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hle))
    omega
  have hlt : i < Nat.log2 (N / w) + 2 := by
    by_contra hge
    have h3 := Nat.mul_le_mul_right w (Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hge))
    have e : 2 ^ (Nat.log2 (N / w) + 2) * w = 2 * (2 ^ (Nat.log2 (N / w) + 1) * w) := by ring
    omega
  have hi : i = Nat.log2 (N / w) + 1 := by omega
  rw [ht, hi]

-- Section 4. The window lemma: the closure of the known set moves from `N` to `N'`.

theorem extend {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y F : List ℕ} {N N' : ℕ}
    (h : St P X Y N) (hchk : winOk X Y F N N' = true) : St P X Y N' := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
  refine ⟨hXP, hXn, hY, fun p hp hpN' => ?_⟩
  by_cases hpN : p < N
  · exact hcl p hp hpN
  by_contra hpX
  simp only [winOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨hN2, hall⟩ := hchk
  have hpp := (C.hP p hp).1
  have hp2 := (C.hP p hp).2
  have hpodd : p % 2 = 1 := by
    rcases hpp.eq_two_or_odd with h2 | h2
    · exact absurd h2 hp2
    · exact h2
  obtain ⟨i, u, hu, hiu⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := p + 1) (by omega) 2 (by norm_num)
  have hu0 : u ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hiu
    omega
  obtain ⟨j, d, hd, hjd⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := u) hu0 5 (by norm_num)
  have hdvd : d ∣ p + 1 := ⟨2 ^ i * 5 ^ j, by rw [hiu, hjd]; ring⟩
  have hprime : ∀ c : ℕ, c.Prime → c ∣ d → c ≠ 2 ∧ c ≠ 5 := fun c _ hcd =>
    ⟨fun h2 => hu (by rw [hjd]; exact (h2 ▸ hcd).mul_left _), fun hz => hd (hz ▸ hcd)⟩
  have hopen : ∀ c : ℕ, c.Prime → c ∣ d → c ∈ opens X := fun c hc hcd => by
    obtain ⟨hc2, hcz⟩ := hprime c hc hcd
    have hcp : c ∣ p + 1 := hcd.trans hdvd
    have hcP : c ∈ P := C.s1 c hc hc2 hcz p hp hcp
    have h2c := two_mul_le hc hc2 hpp hp2 hcp
    have hcX : c ∈ X := hcl c hcP (by omega)
    refine mem_opens hcX (fun e => C.hc13 p hp (e ▸ hcp)) fun x hx hcx => ?_
    exact hpX ((C.s3 c hc hc2 hcz p hp x (hXP x hx) hcp hcx) ▸ hx)
  have hdD : d ∣ (opens X).prod := dvd_of_primes
    (fun c hc hcc => by
      obtain ⟨hc2, hcz⟩ := hprime c hc ((Dvd.intro c rfl : c ∣ c * c).trans hcc)
      exact C.s6 c hc hc2 hcz p hp (hcc.trans hdvd))
    (fun c hc hcd => List.dvd_prod (hopen c hc hcd))
  have hmem : d ∈ subProds (opens X) := mem_subProds _
    (fun c hc => (C.hP c (hXP c (List.mem_filter.mp hc).1)).1) d hdD
  have hjdvd : 5 ^ j ∣ p + 1 := ⟨2 ^ i * d, by rw [hiu, hjd]; ring⟩
  have hjL : j < 2 := by
    by_contra hj
    exact C.led (((pow_dvd_pow 5 (by omega : 2 ≤ j)).trans hjdvd).trans
      (Finset.dvd_prod_of_mem (fun q => q + 1) hp))
  have hi1 : 1 ≤ i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    rw [hi0, pow_zero, one_mul] at hiu
    exact hu ⟨(p + 1) / 2, by omega⟩
  have hw0 : 0 < 5 ^ j * d := Nat.pos_of_ne_zero (by rw [← hjd]; exact hu0)
  have hpw : p + 1 = 2 ^ i * (5 ^ j * d) := by rw [hiu, hjd]
  have hwN : 5 ^ j * d ≤ N := by
    by_contra hNw
    have h2 : 2 ^ 1 * (5 ^ j * d) ≤ 2 ^ i * (5 ^ j * d) :=
      Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hi1)
    omega
  have h1 := hall d hmem j (List.mem_range.mpr hjL)
  rw [Bool.or_eq_true, Bool.or_eq_true] at h1
  rcases h1 with (h1 | h1) | h1
  · have h2 : 5 ^ 2 ∣ 5 ^ j * succProd X := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1)
    have h3 : 5 ^ j * succProd X ∣ (p + 1) * succProd X := Nat.mul_dvd_mul_right hjdvd _
    have h4 := prod_mul_dvd hXP hXn (T := {p}) (Finset.singleton_subset_iff.mpr hp)
      (fun q hq => (Finset.mem_singleton.mp hq) ▸ hpX)
    rw [Finset.prod_singleton] at h4
    exact C.led (h2.trans (h3.trans h4))
  · exact absurd (of_decide_eq_true h1) (not_lt.mpr hwN)
  · have hv : 2 ^ (Nat.log2 (N / (5 ^ j * d)) + 1) * (5 ^ j * d) - 1 = p := by
      rw [pow_window hw0 hwN hpw (by omega) (by omega), Nat.add_sub_cancel]
    rw [hv] at h1
    simp only [candOk, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h1
    rcases h1 with ((h1 | h1) | h1) | ⟨f, -, ⟨hf1, hfp⟩, hmod⟩
    · omega
    · exact hpX h1
    · exact hY p h1 hp
    · rcases (Nat.dvd_prime hpp).mp (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

-- Section 5. The two contradictions.

theorem up_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y : List ℕ} {N : ℕ}
    (h : St P X Y N) (hchk : upOk X = true) : False := by
  obtain ⟨hXP, hXn, -, -⟩ := h
  simp only [upOk, decide_eq_true_eq] at hchk
  have hF : X.toFinset ⊆ P := fun x hx => hXP x (List.mem_toFinset.mp hx)
  have h1 := Finset.prod_sdiff hF (f := fun p => p + 1)
  have h2 := Finset.prod_sdiff hF (f := fun p => p)
  rw [succProd_eq hXn] at h1
  rw [prod_eq hXn] at h2
  have hQ : ∏ p ∈ P \ X.toFinset, p ≤ ∏ p ∈ P \ X.toFinset, (p + 1) :=
    Finset.prod_le_prod (fun i _ => Nat.zero_le _) (fun i _ => Nat.le_succ i)
  have hpos : 0 < ∏ p ∈ P \ X.toFinset, (p + 1) := Finset.prod_pos fun p _ => Nat.succ_pos p
  have hSpos : 0 < succProd X := by
    unfold succProd
    exact List.prod_pos (fun a ha => by
      obtain ⟨x, -, rfl⟩ := List.mem_map.mp ha
      exact Nat.succ_pos x)
  have E := C.E
  rw [← h1, ← h2] at E
  have key : 2 ^ (m + 1) * 25 * ((∏ p ∈ P \ X.toFinset, p) * X.prod) <
      (2 ^ m + 1) * 26 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) :=
    calc 2 ^ (m + 1) * 25 * ((∏ p ∈ P \ X.toFinset, p) * X.prod)
        = 2 ^ m * ((∏ p ∈ P \ X.toFinset, p) * (2 * 25 * X.prod)) := by ring
      _ ≤ 2 ^ m * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (26 * succProd X)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hchk)
      _ < (2 ^ m + 1) * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (26 * succProd X)) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.mul_pos hpos (Nat.mul_pos (by norm_num) hSpos))
      _ = (2 ^ m + 1) * 26 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) := by ring
  exact absurd E.symm (Nat.ne_of_lt key)

theorem balance_q {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (C.hP p hp).1.pos
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) := Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * 26 * ∏ p ∈ P, ((p : ℚ) + 1) = 2 ^ (m + 1) * 25 * ∏ p ∈ P, (p : ℚ) := by
    have h := congrArg (Nat.cast : ℕ → ℚ) C.E
    push_cast at h
    exact h
  have e : ∏ p ∈ P, (1 + 1 / (p : ℚ)) = (∏ p ∈ P, ((p : ℚ) + 1)) / ∏ p ∈ P, (p : ℚ) := by
    rw [← Finset.prod_div_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    have : (0 : ℚ) < p := by exact_mod_cast hpos p hp
    field_simp
  have h2 : (0 : ℚ) < (2 : ℚ) ^ m := by positivity
  rw [e]
  field_simp
  rw [pow_succ] at hcast
  linarith

theorem weight_list : ∀ X : List ℕ, (∀ x ∈ X, 0 < x) →
    (X.map (fun x : ℕ => 1 + 1 / (x : ℚ))).prod = (succProd X : ℚ) / (X.prod : ℚ)
  | [], _ => by simp [succProd]
  | x :: t, h => by
    have hx : (0 : ℚ) < x := by exact_mod_cast h x List.mem_cons_self
    have ht : (0 : ℚ) < (t.prod : ℚ) := by
      exact_mod_cast List.prod_pos (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have ih := weight_list t (fun a ha => h a (List.mem_cons_of_mem _ ha))
    unfold succProd at ih ⊢
    rw [List.map_cons, List.prod_cons, ih, List.map_cons, List.prod_cons, List.prod_cons]
    push_cast
    field_simp

theorem final_ineq {S Pi N E : ℕ} (hN : 5 ≤ N) (hPi : 0 < Pi)
    (h : (2 ^ 64 + 1) * 26 * S * (N + 1) ^ (E + 1) < 2 * 2 ^ 64 * 25 * Pi * (N - 1) ^ E * (N - 3)) :
    (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((S : ℚ) / Pi) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ E *
      (((N : ℚ) + 1) / ((N : ℚ) - 3)) < 2 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 3 := ⟨N - 3, by omega⟩
  have e1 : k + 3 - 1 = k + 2 := by omega
  have e3 : k + 3 - 3 = k := by omega
  rw [e1, e3] at h
  have hq := (Nat.cast_lt (α := ℚ)).mpr h
  push_cast at hq
  have hk : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
  have hPiq : (0 : ℚ) < Pi := by exact_mod_cast hPi
  have hk2 : (0 : ℚ) < (k : ℚ) + 2 := by linarith
  have e : (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((S : ℚ) / Pi) *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 1)) ^ E *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 3)) =
      (((2 : ℚ) ^ 64 + 1) * 26 * S * ((k : ℚ) + 3 + 1) ^ (E + 1)) /
        (2 ^ 64 * 25 * Pi * ((k : ℚ) + 2) ^ E * k) := by
    push_cast
    have e4 : (k : ℚ) + 3 - 1 = k + 2 := by ring
    have e5 : (k : ℚ) + 3 - 3 = k := by ring
    rw [e4, e5, div_pow]
    field_simp
    ring
  rw [e, div_lt_iff₀ (by positivity)]
  linarith

theorem low_kill {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y : List ℕ} {N : ℕ}
    (h : St P X Y N) (hchk : lowOk X N = true) : False := by
  obtain ⟨hXP, hXn, -, hcl⟩ := h
  simp only [lowOk, Bool.and_eq_true, decide_eq_true_eq] at hchk
  obtain ⟨hN5, hnum⟩ := hchk
  classical
  obtain ⟨g, hg⟩ := exists_child ({5} : Finset ℕ)
  have hnz : ∀ {c : ℕ}, c ∉ ({5} : Finset ℕ) → c ≠ 5 := fun h h' => h (Finset.mem_singleton.mpr h')
  have hQP : ∀ q ∈ P.filter (fun p => p ∉ X), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hQX : ∀ q ∈ P.filter (fun p => p ∉ X), q ∉ X := fun q hq => (Finset.mem_filter.mp hq).2
  have hQN : ∀ q ∈ P.filter (fun p => p ∉ X), N ≤ q := fun q hq => by
    by_contra hlt
    exact hQX q hq (hcl q (hQP q hq) (by omega))
  have hgp : ∀ p ∈ P, g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ≠ 5 ∧ g p ∈ P ∧ 2 * g p ≤ p + 1 :=
    fun p hp h1 => by
      obtain ⟨hc, hc2, hcN⟩ := (hg p).2.2.1 h1
      exact ⟨hc, hc2, hnz hcN, C.s1 _ hc hc2 (hnz hcN) p hp (hg p).1,
        two_mul_le hc hc2 (C.hP p hp).1 (C.hP p hp).2 (hg p).1⟩
  have hg1 : ∀ q ∈ P.filter (fun p => p ∉ X), g q ∈ P.filter (fun p => p ∉ X) → g q ≠ 1 :=
    fun q _ hgq h1 => by
      have := (C.hP _ (hQP _ hgq)).1
      rw [h1] at this
      exact Nat.not_prime_one this
  have hpath := path_bound g (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1)) (P.filter (fun p => p ∉ X)).card
    (P.filter (fun p => p ∉ X)) rfl
    (fun q hq => (C.hP q (hQP q hq)).1.pos)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      have := hc.two_le
      omega)
    (fun q hq q' hq' hgq he => by
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact C.s3 _ hc hc2 hcz q (hQP q hq) q' (hQP q' hq') (hg q).1 (he ▸ (hg q').1))
    (fun q hq => one_add_le_B (C.hP q (hQP q hq)).1.two_le)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact B_step hc.two_le h2)
  generalize hRdef : (P.filter (fun p => p ∉ X)).filter (fun q => g q ∉ P.filter (fun p => p ∉ X)) = R at hpath
  have hRQ : ∀ q ∈ R, q ∈ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).1
  have hRg : ∀ q ∈ R, g q ∉ P.filter (fun p => p ∉ X) := fun q hq => by
    rw [← hRdef] at hq
    exact (Finset.mem_filter.mp hq).2
  have hRP : ∀ q ∈ R, q ∈ P := fun q hq => hQP q (hRQ q hq)
  have hA : ∀ q ∈ R, g q ≠ 1 → g q ∈ opens X := fun q hq h1 => by
    have hqP := hRP q hq
    obtain ⟨hc, hc2, hcz, hcP, -⟩ := hgp q hqP h1
    have hcX : g q ∈ X := by
      by_contra hcX
      exact hRg q hq (Finset.mem_filter.mpr ⟨hcP, hcX⟩)
    refine mem_opens hcX (fun e => C.hc13 q hqP (e ▸ (hg q).1))
      fun x hx hcx => ?_
    exact hQX q (hRQ q hq) ((C.s3 _ hc hc2 hcz q hqP x (hXP x hx) (hg q).1 hcx) ▸ hx)
  have hN2 : (2 : ℚ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hβN : ∀ q ∈ R, ((q : ℚ) + 1) / ((q : ℚ) - 1) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := fun q hq =>
    B_anti (by omega) (hQN q (hRQ q hq))
  have hβ0 : ∀ q ∈ R, (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq =>
    B_nonneg (C.hP q (hRP q hq)).1.pos
  have hBN1 : (1 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  have hcardA : (R.filter (fun q => g q ≠ 1)).card ≤ (opens X).length := by
    refine (Finset.card_le_card_of_injOn g (t := (opens X).toFinset) ?_ ?_).trans (List.toFinset_card_le _)
    · intro q hq
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      exact Finset.mem_coe.mpr (List.mem_toFinset.mpr (hA q hqR h1))
    · intro q hq q' hq' he
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      obtain ⟨hqR', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
      obtain ⟨hc, hc2, hcz, -, -⟩ := hgp q (hRP q hqR) h1
      exact C.s3 _ hc hc2 hcz q (hRP q hqR) q' (hRP q' hqR') (hg q).1 (he ▸ (hg q').1)
  have hledB : ¬ 5 ^ 2 ∣ 5 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card * succProd X :=
    fun hd => by
      have hsub : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1), q ∈ R := fun q hq =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      have h1 := prod_mul_dvd hXP hXn (T := (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1))
        (fun q hq => hRP q (hsub q hq)) (fun q hq => hQX q (hRQ q (hsub q hq)))
      have h2 : 5 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ∣
          ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1), (q + 1) := by
        rw [← Finset.prod_const]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun q hq => (Finset.mem_filter.mp hq).2
      exact C.led (hd.trans ((Nat.mul_dvd_mul_right h2 _).trans h1))
  have hcardB : ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ≤ ledgerLeft X := by
    unfold ledgerLeft
    by_contra hlt
    apply hledB
    split_ifs at hlt with h1
    · exact pow_mul_dvd (by omega) (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1))
    · exact pow_mul_dvd (by omega : 2 ≤ _) (Dvd.intro _ rfl)
  have hpow : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1), ∃ k, q + 1 = 2 ^ k :=
    fun q hq => by
      obtain ⟨hq1, hzq⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hg1'⟩ := Finset.mem_filter.mp hq1
      refine two_pow_of_no_odd_prime fun c hc hc2 hcd => ?_
      have := (hg q).2.1 (not_not.mp hg1') c hc hc2 hcd
      rw [Finset.mem_singleton] at this
      exact hzq (this ▸ hcd)
  have hprodC : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 5 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    refine tail_bound _ _ N rfl (by omega)
      (fun q hq => hQN q (hRQ q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1))
      (fun q hq q' hq' hlt => ?_)
    obtain ⟨k, hk⟩ := hpow q hq
    obtain ⟨k', hk'⟩ := hpow q' hq'
    have hkk : k < k' := by
      by_contra hge
      have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (not_lt.mp hge)
      omega
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) (Nat.succ_le_of_lt hkk)
    rw [pow_succ] at this
    omega
  have hprodA : ∏ q ∈ R.filter (fun q => g q ≠ 1), (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp hq).1)
      (fun q hq => hβN q (Finset.mem_filter.mp hq).1)
  have hprodB : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (fun q hq => hβN q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  have hsplit1 := Finset.prod_filter_mul_prod_filter_not R (fun q => g q ≠ 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (R.filter (fun q => ¬ g q ≠ 1)) (fun q => 5 ∣ q + 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hpowle : (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card *
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 5 ∣ q + 1)).card ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) := by
    rw [← pow_add]
    exact pow_le_pow_right₀ hBN1 (Nat.add_le_add hcardA hcardB)
  have hT0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 3) := by
    have : (5 : ℚ) ≤ N := by exact_mod_cast hN5
    exact div_nonneg (by linarith) (by linarith)
  have hB0 : (0 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := le_trans zero_le_one hBN1
  have hRbound : ∏ q ∈ R, (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    rw [← hsplit1, ← hsplit2, ← mul_assoc]
    refine mul_le_mul (le_trans (mul_le_mul hprodA hprodB ?_ (pow_nonneg hB0 _)) hpowle) hprodC ?_
      (pow_nonneg hB0 _)
    · exact Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
    · exact Finset.prod_nonneg fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
  have hXpos : ∀ x ∈ X, 0 < x := fun x hx => (C.hP x (hXP x hx)).1.pos
  have hfil : P.filter (fun p => p ∈ X) = X.toFinset := by
    ext x
    rw [Finset.mem_filter, List.mem_toFinset]
    exact ⟨fun h => h.2, fun h => ⟨hXP x h, h⟩⟩
  have hsplitP := Finset.prod_filter_mul_prod_filter_not P (fun p => p ∈ X) (fun p => 1 + 1 / (p : ℚ))
  rw [hfil, List.prod_toFinset _ hXn, weight_list X hXpos] at hsplitP
  have hbal := balance_q C
  rw [← hsplitP] at hbal
  have hPipos : 0 < X.prod := List.prod_pos hXpos
  have hfin := final_ineq hN5 hPipos hnum
  have hm64 : (1 : ℚ) / 2 ^ m ≤ 1 / 2 ^ 64 :=
    one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ (by norm_num) C.hm)
  have hSq : (0 : ℚ) ≤ (succProd X : ℚ) / (X.prod : ℚ) := div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hQle := hpath.trans hRbound
  have hQ0 : (0 : ℚ) ≤ ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) :=
    Finset.prod_nonneg fun p _ => by positivity
  have hchain : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) *
      ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ))) ≤
      (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((succProd X : ℚ) / (X.prod : ℚ)) *
        (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    have h1 : (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) ≤ (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h2 : (succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) ≤
        (succProd X : ℚ) / (X.prod : ℚ) * ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
          (((N : ℚ) + 1) / ((N : ℚ) - 3))) := mul_le_mul_of_nonneg_left hQle hSq
    calc (1 + 1 / (2 : ℚ) ^ m) * (26 / 25) *
        ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)))
        ≤ (1 + 1 / (2 : ℚ) ^ 64) * (26 / 25) * ((succProd X : ℚ) / (X.prod : ℚ) *
          ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
            (((N : ℚ) + 1) / ((N : ℚ) - 3)))) :=
          mul_le_mul h1 h2 (mul_nonneg hSq hQ0) (by positivity)
      _ = _ := by ring
  linarith

-- Section 6. Search trees as data, and their checker.

/-- A search tree: `U` and `L` are the two contradictions, `W N' F t` moves the closure to `N'` (with the factors
`F`) and goes on with `t`, `B y t1 t2` splits on whether `y` is a simple prime. -/
inductive T where
  | U : T
  | L : T
  | W : ℕ → List ℕ → T → T
  | B : ℕ → T → T → T

/-- The checker of a tree at the state `X`, `Y`, `N`. -/
def chk : T → List ℕ → List ℕ → ℕ → Bool
  | T.U, X, _, _ => upOk X
  | T.L, X, _, N => lowOk X N
  | T.W N' F t, X, Y, N => winOk X Y F N N' && chk t X Y N'
  | T.B y t1 t2, X, Y, N => decide (y ∉ X) && chk t1 (y :: X) Y N && chk t2 X (y :: Y) N

theorem sound {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    ∀ (t : T) (X Y : List ℕ) (N : ℕ), chk t X Y N = true → St P X Y N → False
  | T.U, _, _, _, h, hs => up_kill C hs h
  | T.L, _, _, _, h, hs => low_kill C hs h
  | T.W N' F t, X, Y, N, h, hs => by
    rw [chk, Bool.and_eq_true] at h
    exact sound C t X Y N' h.2 (extend C hs h.1)
  | T.B y t1 t2, X, Y, N, h, hs => by
    rw [chk, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    by_cases hy : y ∈ P
    · exact sound C t1 (y :: X) Y N h.1.2 (incl hs hy h.1.1)
    · exact sound C t2 X (y :: Y) N h.2 (excl hs hy)

-- Section 7. The search tree (found by an exact search; the kernel runs the checker on it).

set_option maxRecDepth 1000000 in
/-- The search tree: 2227 nodes (1113 splits, 82 upper and 1032 lower contradictions), 2353 windows. -/
def tree : T :=
  (.W 3 [] (.B 3 (.W 5 [] (.W 9 [] (.W 11 [3] (.B 11 (.W 19 [3] (.B 19 (.W 31 [3] (.B 31 .U (.W 37 [] (.B 37
  .U (.W 43 [] (.B 43 .U (.W 85 [3] (.W 127 [3] (.B 127 (.W 151 [] (.B 151 (.W 301 [3, 5, 11] (.W 601 [3, 7]
  (.W 1201 [3, 5, 19] (.W 2401 [3, 17, 23] .L)))) (.W 301 [3, 5, 11] (.W 601 [3, 7] (.W 607 [] (.B 607 (.W
  1213 [3, 5, 19] .L) (.W 1213 [3, 5, 19] .L))))))) (.W 151 [] (.B 151 (.W 301 [3, 5] (.W 601 [3, 7] .L)) (.W
  301 [3, 5] (.W 601 [3, 7] .L))))))))))))) (.W 31 [3] (.B 31 (.W 43 [3] (.B 43 (.W 61 [] (.B 61 (.W 79 [3]
  (.B 79 .U (.W 127 [5, 11] (.B 127 .U (.W 253 [3] (.W 487 [3, 7, 11] (.B 487 .U (.W 859 [3, 7] (.B 859 .U
  (.W 1279 [3, 23] (.B 1279 .U (.W 1951 [3, 5] (.B 1951 (.W 3901 [3, 19, 23] (.W 5119 [3, 47] (.B 5119 .U (.W
  5503 [] (.B 5503 .U (.W 8191 [3] (.B 8191 .U (.W 13759 [3] (.B 13759 (.W 15607 [] (.B 15607 .U (.W 31213
  [3, 7] (.W 62425 [3, 7] (.W 124849 [3, 13, 149] (.W 131071 [3] (.B 131071 (.W 249727 [3] (.B 249727 .U (.W
  499453 [3, 11, 19] (.W 524287 [3] (.B 524287 (.W 1048573 [3, 13, 967] (.W 1048573 [] (.B 1048573 .U (.W
  2097145 [3, 7] (.W 3995647 [3, 7] (.B 3995647 (.W 4194271 [] (.B 4194271 .U (.W 8388541 [3, 5, 929, 2647]
  (.W 16777081 [3, 47] (.W 16777183 [71] (.B 16777183 .U (.W 33554365 [3, 5, 79] (.W 67108351 [3, 31] (.B
  67108351 (.W 134216701 [3, 5, 7, 23] (.W 268433401 [3, 7, 31] (.W 536866801 [3, 5, 7, 13] (.W 536866807 []
  (.B 536866807 (.W 1073733613 [3, 233] (.W 2147467225 [3, 5, 29, 311, 659] .L)) (.W 1073733613 [3, 233] (.W
  2147467225 [3, 5, 311, 659] .L))))))) (.W 134216701 [3, 5, 7, 23] (.W 268433401 [3, 7] (.W 536866801 [3, 5,
  7, 11, 13] .L)))))))))))) (.W 4194271 [] (.B 4194271 (.W 8388541 [3, 5, 929] (.W 16777081 [3, 7, 19, 47]
  (.W 16777183 [3] (.B 16777183 .U (.W 33554167 [3, 79] (.B 33554167 (.W 67108333 [3, 31, 103, 3109] (.W
  134216665 [3, 5, 7, 17] (.W 255721471 [3, 7, 13] (.B 255721471 (.W 511442941 [3, 5, 7, 13] (.W 511442941 []
  (.B 511442941 (.W 1022885881 [3, 233] (.W 1073733343 [19] (.B 1073733343 (.W 2147466685 [3, 5, 311] (.W
  2147483647 [3, 5] (.B 2147483647 (.W 4294967293 [3, 17, 59] (.W 8589934585 [3, 7, 17, 9241] (.W 17179869169
  [3, 5, 7] (.W 34359738337 [3, 5, 43] (.W 68719476673 [3, 31, 797, 20897, 23039] (.W 137438953345 [3, 7, 17,
  19] .L)))))) (.W 4294967293 [3, 17, 59] (.W 8589934585 [3, 7, 17] (.W 17179869169 [3, 5, 7] (.W 34359738337
  [3, 5, 43] .L))))))) (.W 2147466685 [3, 5, 311] (.W 2147483647 [3] (.B 2147483647 (.W 4294967293 [3, 5, 17,
  59] (.W 8589934585 [3, 7, 9241] (.W 17179869169 [3, 5, 7, 17] .L))) (.W 4294967293 [3, 5, 17, 59] (.W
  8589934585 [3, 7] .L)))))))) (.W 1022885881 [3, 233] (.W 1073733343 [3] (.B 1073733343 (.W 2147466685 [3,
  5, 13, 311] (.W 2147483647 [3, 5] (.B 2147483647 (.W 4294967293 [3, 59] (.W 8589934585 [3, 7, 17, 9241]
  .L)) (.W 4294967293 [3, 59] (.W 8589934585 [3, 7, 17] .L))))) (.W 2147466685 [3, 5, 13, 311] (.W 2147483647
  [3] (.B 2147483647 (.W 4294967293 [3, 5, 59] (.W 8589934585 [3, 7, 17, 9241] .L)) (.W 4294967293 [3, 5, 59]
  .L)))))))))) (.W 511442941 [3, 5, 7, 13] (.W 1022885881 [3, 233, 659] (.W 1073733343 [7417] (.B 1073733343
  (.W 2147466685 [3, 5, 307, 311] .L) (.W 2147466685 [3, 5, 307, 311] .L))))))))) (.W 67108333 [3, 31, 103,
  3109] (.W 134216665 [3, 5, 7] (.W 255721471 [3, 7, 13, 229] (.B 255721471 (.W 511442941 [3, 7, 13] .L) (.W
  511442941 [3, 7, 13] .L))))))))))) (.W 8388541 [3, 5, 929] (.W 16777081 [3, 19, 47] (.W 16777183 [71] (.B
  16777183 (.W 33554365 [3, 79] (.W 67108351 [3, 5, 31, 103, 3109] (.B 67108351 .L .L))) (.W 33554365 [3, 79]
  (.W 67108351 [3, 31, 103, 3109] (.B 67108351 .L .L))))))))))))))) (.W 1048573 [3, 13, 967] (.W 2097145 [3,
  7] (.W 3995647 [3, 7] (.B 3995647 (.W 4194271 [] (.B 4194271 (.W 8388541 [3, 929, 2647] .L) (.W 8388541 [3,
  929, 2647] .L))) (.W 4194271 [] (.B 4194271 (.W 8388541 [3, 929] .L) (.W 8388541 [3, 929] .L))))))))))))
  (.W 249727 [3] (.B 249727 (.W 499453 [3, 19] (.W 524287 [19] (.B 524287 (.W 1048573 [3] (.W 1048573 [] (.B
  1048573 (.W 2097145 [3, 5, 7] (.W 4194289 [3, 5, 7] .L)) (.W 2097145 [3, 5, 7] (.W 4194289 [3, 7] .L)))))
  (.W 1048573 [3] (.W 2097145 [3, 5, 7] .L))))) (.W 499453 [3, 19] (.W 524287 [3] (.B 524287 (.W 1048573 [3,
  967] (.W 1048573 [] (.B 1048573 (.W 2097145 [3, 7] .L) (.W 2097145 [3, 7] .L)))) (.W 1048573 [3, 967]
  .L))))))))))))) (.W 15607 [] (.B 15607 (.W 20479 [3] (.B 20479 .U (.W 40957 [3, 5, 7] (.W 81913 [3, 23] (.W
  81919 [] (.B 81919 (.W 131071 [5, 83] (.B 131071 .U (.W 262141 [3, 19] (.W 499423 [3, 5] (.B 499423 (.W
  524287 [] (.B 524287 (.W 655351 [] (.B 655351 (.W 1048573 [3, 5] (.B 1048573 .U (.W 2097145 [3, 7] (.W
  4194289 [3, 7] (.W 5242807 [3, 5] (.B 5242807 (.W 10485613 [3, 5, 47] (.W 10485613 [] (.B 10485613 (.W
  16777183 [3, 5] (.B 16777183 (.W 33554365 [3, 5, 41] .L) (.W 33554365 [3, 5, 41] .L))) (.W 16777183 [3, 5]
  (.B 16777183 (.W 33554365 [3, 41] .L) (.W 33554365 [3, 41] .L)))))) (.W 10485613 [3, 5, 47] (.W 16777183
  [3, 5] (.B 16777183 .L .L))))))))) (.W 1048573 [3, 5] (.B 1048573 (.W 2097145 [3, 7] (.W 4194289 [3, 5, 7,
  127] (.W 7045033 [3, 5] (.B 7045033 (.W 14090065 [3, 7, 47] .L) (.W 14090065 [3, 7, 13, 47] .L))))) (.W
  2097145 [3, 7] (.W 4194289 [3, 7, 127] (.W 7045033 [3, 5] (.B 7045033 .L .L)))))))) (.W 655351 [] (.B
  655351 (.W 1310701 [3, 5] (.W 2621401 [3, 7] (.W 5242801 [3, 7] .L))) (.W 1310701 [3, 5] (.W 2621401 [3, 7]
  .L)))))) (.W 524287 [] (.B 524287 (.W 655351 [] (.B 655351 (.W 1048573 [3] (.B 1048573 (.W 2097145 [3, 5,
  7] (.W 4194289 [3, 5, 7] (.W 5242807 [3] (.B 5242807 (.W 10485613 [5, 7, 47, 59, 71] .L) (.W 10485613 [5,
  7, 47, 59, 71] .L))))) (.W 2097145 [3, 5, 7] (.W 4194289 [3, 7] (.W 5242807 [3, 5] (.B 5242807 .L .L))))))
  (.W 1048573 [3] (.B 1048573 (.W 2097145 [3, 5, 7] (.W 4194289 [3, 5, 7, 127] .L)) (.W 2097145 [3, 5, 7] (.W
  4194289 [3, 7, 127] .L)))))) (.W 655351 [] (.B 655351 (.W 1310701 [3] (.W 2621401 [5, 7] .L)) (.W 1310701
  [3] (.W 2621401 [3, 5, 7] .L))))))))))) (.W 131071 [3, 5, 83] (.B 131071 (.W 262141 [3, 137] (.W 499423 [3,
  5, 11, 31] (.B 499423 (.W 524287 [3] (.B 524287 (.W 1048573 [3, 5, 13, 41] (.W 1048573 [] (.B 1048573 (.W
  1310719 [3] (.B 1310719 (.W 2621437 [3, 5, 7] (.W 4194271 [3, 7] (.B 4194271 .L .L))) (.W 2621437 [3, 5, 7,
  311] .L))) (.W 1310719 [3] (.B 1310719 (.W 2621437 [3, 7] .L) (.W 2621437 [3, 7, 311] .L)))))) (.W 1048573
  [3, 5, 13, 41] (.W 1310719 [3] (.B 1310719 (.W 2621437 [3, 7] .L) (.W 2621437 [3, 7, 311] .L)))))) (.W
  524287 [3] (.B 524287 (.W 1048573 [3, 13, 41] (.W 1048573 [] (.B 1048573 (.W 1310719 [3, 13] (.B 1310719
  (.W 2621437 [3, 5, 7] .L) (.W 2621437 [3, 5, 7, 311] .L))) (.W 1310719 [3, 13] (.B 1310719 (.W 2621437 [3,
  5, 7] .L) (.W 2621437 [3, 5, 7, 311] .L)))))) (.W 1048573 [3, 13, 41] (.W 1310719 [3, 13] (.B 1310719 .L
  .L)))))))) (.W 262141 [3, 137] (.W 499423 [3, 5, 11, 31] (.B 499423 (.W 524287 [] (.B 524287 (.W 1048573
  [3, 5, 41] .L) (.W 1048573 [3, 5, 41] .L))) (.W 524287 [] (.B 524287 (.W 1048573 [3, 41] .L) (.W 1048573
  [3, 41] .L)))))))))))))) (.W 20479 [3] (.B 20479 (.W 40957 [3, 5, 7] (.W 81913 [3, 7, 149] (.W 131071 [3,
  83] (.B 131071 (.W 249727 [3, 5, 173] (.B 249727 (.W 499453 [3, 5, 11] (.W 524287 [3, 19] (.B 524287 (.W
  1048573 [3, 13, 67] .L) (.W 1048573 [3, 13, 67] .L)))) (.W 499453 [3, 5, 11] .L))) (.W 249727 [3, 5, 173]
  (.B 249727 (.W 499453 [3, 5] .L) (.W 499453 [3, 5] .L))))))) (.W 39019 [3, 5, 7] (.B 39019 (.W 78037 [3]
  (.W 131071 [73, 83] (.B 131071 (.W 262141 [3] .L) (.W 262141 [3] .L)))) (.W 78037 [3, 23, 149] (.W 81919
  [3] (.B 81919 (.W 131071 [3, 83] (.B 131071 (.W 249727 [3, 5, 19] (.B 249727 .L .L)) (.W 249727 [3, 5, 19]
  (.B 249727 .L .L)))) (.W 131071 [3, 83] (.B 131071 (.W 249727 [3, 5, 7, 137] (.B 249727 .L .L))
  .L)))))))))))))))))))) (.W 3901 [3, 19, 23] (.W 5119 [3, 7] (.B 5119 (.W 5503 [5] (.B 5503 (.W 8191 [37]
  (.B 8191 (.W 16381 [3, 5, 29] (.W 16381 [] (.B 16381 (.W 31231 [3] (.B 31231 (.W 62461 [7, 31, 181] (.W
  124921 [3, 7] (.W 131071 [3, 7] (.B 131071 .U (.W 262141 [3, 5, 7, 13] (.W 524281 [3, 19] (.W 524287 [] (.B
  524287 (.W 1048573 [3, 17, 43, 97] (.W 1048573 [] (.B 1048573 .U (.W 2097145 [3, 233] (.W 2620927 [3, 7]
  (.B 2620927 (.W 5241853 [3, 5, 7] (.W 10483705 [3, 7, 19, 47] (.W 16777183 [3, 11, 31] (.B 16777183 (.W
  33548287 [3, 5] (.B 33548287 (.W 67096573 [3, 5, 19, 31] .L) (.W 67096573 [3, 5, 19, 31] .L))) (.W 33548287
  [3, 5] (.B 33548287 .L .L)))))) (.W 5241853 [3, 5, 7] (.W 10483705 [3, 7, 47] (.W 16777183 [3, 7, 11, 31]
  (.B 16777183 (.W 33548287 [3] (.B 33548287 .L .L)) (.W 33548287 [3] (.B 33548287 .L .L)))))))))))) (.W
  1048573 [3, 17, 43, 97] (.W 2097145 [3, 233] (.W 2620927 [7] (.B 2620927 (.W 5241853 [3, 5, 7] .L) (.W
  5241853 [3, 5, 7] .L))))))))))))) (.W 62461 [7, 31, 181] (.W 124921 [3] (.W 131071 [7, 11] (.B 131071 (.W
  262141 [3, 5, 7] (.W 499711 [3, 11] (.B 499711 (.W 524287 [3, 19] (.B 524287 (.W 1048573 [3, 13, 17, 43,
  53] .L) (.W 1048573 [3, 13, 17, 43, 53] .L))) (.W 524287 [3, 19] (.B 524287 (.W 624517 [] (.B 624517 .L (.W
  1048573 [3, 5, 13, 17, 43] (.B 1048573 .L .L)))) .L))))) (.W 262141 [3, 5, 7] (.W 499711 [3] (.B 499711 .L
  .L))))))))) (.W 31231 [3] (.B 31231 (.W 62461 [3, 7, 31] (.W 124921 [3, 7] (.W 131071 [3] (.B 131071 (.W
  262111 [5, 7, 13] (.B 262111 (.W 524221 [3, 11] .L) .L)) (.W 262111 [5, 7, 13] (.B 262111 .L .L)))))) (.W
  62461 [3, 7, 31] (.W 124921 [3, 7] (.W 131071 [3, 11] (.B 131071 (.W 262111 [3, 5, 7] (.B 262111 .L .L))
  .L))))))))) (.W 16381 [3, 5, 29] (.W 31231 [3] (.B 31231 (.W 62461 [7, 31] .L) (.W 62461 [7, 31] .L))))))
  (.W 8191 [37] (.B 8191 (.W 16381 [3, 29] (.W 16381 [] (.B 16381 (.W 20983 [3] (.B 20983 (.W 41965 [7, 31,
  181] (.W 83929 [3, 5] .L)) (.W 31231 [5] (.B 31231 (.W 62461 [3, 7, 31, 181] (.W 124921 [3, 7, 83] .L)) (.W
  62461 [3, 7, 31, 181] .L))))) (.W 20983 [3] (.B 20983 (.W 41965 [3, 7, 31] (.W 83929 [3, 5, 7] .L)) (.W
  31231 [5] (.B 31231 (.W 62461 [3, 7, 31] .L) (.W 62461 [3, 7, 31] .L)))))))) (.W 16381 [3, 29] (.W 20983
  [3] (.B 20983 (.W 41965 [7, 31] .L) (.W 31231 [5] (.B 31231 .L .L))))))))) (.W 5503 [5] (.B 5503 (.W 8191
  [37] (.B 8191 (.W 16381 [3, 5] (.W 16381 [] (.B 16381 (.W 20479 [3, 131] (.B 20479 (.W 31231 [3] (.B 31231
  (.W 62461 [7, 181] (.W 124921 [3, 7] .L)) (.W 62461 [7, 181] (.W 124921 [3] .L)))) (.W 31231 [3] (.B 31231
  (.W 62461 [3, 7, 181] .L) (.W 62461 [3, 7, 181] .L))))) (.W 20479 [3, 131] (.B 20479 (.W 31231 [3] (.B
  31231 (.W 62461 [3, 7] .L) (.W 62461 [3, 7] .L))) (.W 31231 [3] (.B 31231 (.W 62461 [3, 7] .L) (.W 62461
  [3, 7] .L)))))))) (.W 16381 [3, 5] (.W 20479 [3, 131] (.B 20479 (.W 31231 [3] (.B 31231 .L .L)) (.W 31231
  [3] (.B 31231 .L .L))))))) (.W 8191 [3, 37] (.B 8191 (.W 13759 [3] (.B 13759 (.W 16381 [3] (.B 16381 (.W
  31231 [3, 7] (.B 31231 (.W 62461 [3, 7, 181] .L) .L)) (.W 31231 [3, 7] (.B 31231 .L .L)))) (.W 16381 [3]
  (.B 16381 (.W 20479 [3, 131] (.B 20479 (.W 20983 [] (.B 20983 (.W 41965 [7, 181] .L) (.W 31231 [5] (.B
  31231 (.W 62461 [3, 7, 181] .L) (.W 62461 [3, 7, 181] .L))))) (.W 20983 [] (.B 20983 (.W 41965 [3, 7, 181]
  .L) (.W 31231 [3, 5] (.B 31231 (.W 62461 [3, 7, 23, 181] .L) .L)))))) (.W 20479 [3, 131] (.B 20479 (.W
  20983 [] (.B 20983 (.W 41965 [3, 7] .L) (.W 31231 [5] (.B 31231 .L .L)))) (.W 20983 [] (.B 20983 (.W 41965
  [3, 7] .L) (.W 31231 [3, 5] (.B 31231 .L .L)))))))))) (.W 13759 [3] (.B 13759 (.W 27517 [3] .L) (.W 20479
  [3, 131] (.B 20479 .L .L)))))))))))))))))))))))) (.W 79 [3] (.B 79 (.W 127 [3, 5] (.B 127 .U (.W 157 [] (.B
  157 .U (.W 313 [3, 13] (.W 625 [3, 7] (.W 631 [] (.B 631 (.W 991 [3] (.B 991 (.W 1981 [3, 5, 13] (.W 3961
  [3, 7, 23] (.W 5503 [3, 7] (.B 5503 (.W 7927 [] (.B 7927 .L .L)) (.W 7927 [] (.B 7927 .L .L)))))) (.W 1981
  [3, 5, 13] (.W 3961 [3, 5, 23] .L)))) (.W 991 [3] (.B 991 (.W 1981 [3, 5] (.W 3961 [3, 7, 23] .L)) (.W 1981
  [3, 5] (.W 3961 [3, 5, 7, 23] .L)))))))))))) (.W 127 [3, 5] (.B 127 (.W 253 [3, 13] (.W 505 [3, 7, 11] (.W
  619 [3, 7] (.B 619 (.W 1237 [3, 5] (.W 1237 [] (.B 1237 (.W 2473 [3, 5, 23] .L) (.W 2473 [3, 5, 23] .L))))
  (.W 859 [3] (.B 859 (.W 991 [] (.B 991 (.W 1981 [3, 5, 17] .L) (.W 1981 [3, 5, 17] .L))) (.W 991 [] (.B 991
  (.W 1279 [3, 5] (.B 1279 (.W 2557 [3, 5, 7, 23] .L) (.W 2539 [3, 5, 7, 23] (.B 2539 .L .L)))) (.W 1279 [3,
  5] (.B 1279 (.W 2557 [3, 5, 23] .L) (.W 2539 [3, 5, 23, 37] (.B 2539 .L .L)))))))))))) (.W 253 [3, 13] (.W
  505 [3, 7, 11] (.W 619 [7] (.B 619 .L .L)))))))))) (.W 61 [] (.B 61 (.W 79 [3] (.B 79 (.W 127 [3, 11] (.B
  127 (.W 157 [] (.B 157 .U (.W 313 [3, 5, 11] (.W 487 [3] (.B 487 (.W 631 [3, 7] (.B 631 .U (.W 1261 [3, 5,
  7, 19] (.W 2521 [3, 23] (.W 5041 [3, 5, 7, 17] (.W 8191 [3, 37] (.B 8191 (.W 10111 [] (.B 10111 (.W 15583
  [3, 7] (.B 15583 (.W 16381 [5] (.B 16381 (.W 32761 [3, 5, 7, 73] .L) (.W 32761 [3, 5, 7, 73] .L))) (.W
  16381 [5] (.B 16381 (.W 32761 [3, 7, 73] .L) .L)))) (.W 13903 [3, 7] (.B 13903 .L (.W 15583 [] (.B 15583 .L
  .L)))))) (.W 10111 [] (.B 10111 (.W 15583 [3, 7] (.B 15583 .L .L)) (.W 13903 [3, 7] (.B 13903 .L
  .L))))))))))) (.W 631 [3, 7] (.B 631 (.W 1261 [3, 5, 19] (.W 1951 [3, 13] (.B 1951 (.W 3901 [3, 5, 23] (.W
  7801 [3, 7, 17, 37, 47] (.W 8191 [3] (.B 8191 (.W 15607 [3, 7] (.B 15607 (.W 16381 [5] (.B 16381 (.W 27763
  [3, 7, 61] (.B 27763 .L .L)) .L)) .L)) (.W 15607 [3, 7] (.B 15607 .L .L)))))) (.W 2683 [3, 23] (.B 2683 (.W
  5365 [3, 7, 17] (.W 8191 [3, 5] (.B 8191 (.W 16381 [3, 5] .L) (.W 16381 [3, 5] .L)))) (.W 5365 [3, 5, 7,
  17] (.W 8191 [3, 37] (.B 8191 (.W 15493 [3, 5, 7] (.B 15493 .L .L)) .L)))))))) (.W 1261 [3, 5, 19] (.W 1951
  [3] (.B 1951 (.W 3901 [3, 5, 7, 23] (.W 7801 [3, 17, 37, 47] .L)) (.W 2683 [3, 7, 23] (.B 2683 (.W 5365 [3,
  17] .L) (.W 5365 [3, 5, 17] .L))))))))))))) (.W 157 [] (.B 157 (.W 313 [3, 5] (.W 313 [] (.B 313 (.W 487
  [3] (.B 487 .U (.W 973 [5, 7, 19] (.W 1945 [3] (.W 1951 [] (.B 1951 (.W 2503 [23] (.B 2503 (.W 5005 [3, 5,
  47] (.W 8191 [3, 5] (.B 8191 (.W 15607 [3, 7] (.B 15607 (.W 16381 [] (.B 16381 (.W 20023 [3] (.B 20023 (.W
  40045 [3, 7, 181] (.W 80089 [3, 5] .L)) (.W 40045 [3, 7, 181] .L))) (.W 20023 [3] (.B 20023 (.W 40045 [3,
  7] .L) (.W 40045 [3, 7] .L))))) (.W 16381 [] (.B 16381 (.W 20023 [3] (.B 20023 (.W 40045 [3, 7, 181] .L)
  (.W 40045 [3, 7, 181] .L))) (.W 20023 [3] (.B 20023 (.W 40045 [3, 7] .L) (.W 40045 [3, 7] .L))))))) (.W
  15607 [3, 7] (.B 15607 (.W 20023 [3] (.B 20023 (.W 40045 [3, 7] .L) (.W 40045 [3, 7] .L))) (.W 20023 [3]
  (.B 20023 .L .L))))))) (.W 5005 [3, 5, 47] (.W 8191 [3] (.B 8191 (.W 15607 [5, 7, 47] (.B 15607 (.W 16381
  [] (.B 16381 (.W 32761 [3, 7] .L) .L)) .L)) (.W 15607 [5, 7, 47] (.B 15607 .L .L))))))) (.W 2503 [23] (.B
  2503 (.W 2683 [] (.B 2683 (.W 5365 [3, 5] (.W 8191 [5] (.B 8191 (.W 16381 [3] (.W 16381 [] (.B 16381 (.W
  20023 [3] (.B 20023 (.W 40045 [7, 13, 181] .L) .L)) (.W 20023 [3] (.B 20023 .L .L))))) (.W 16381 [3] .L))))
  (.W 5365 [3, 5] (.W 8191 [3, 37] (.B 8191 (.W 16381 [3, 5, 7] .L) (.W 16381 [3, 5, 7] .L)))))) (.W 2683 []
  (.B 2683 (.W 5365 [3] (.W 8191 [5] (.B 8191 (.W 16381 [3, 5] .L) .L))) (.W 5365 [3, 5] (.W 8191 [3, 37] (.B
  8191 (.W 16381 [3, 5, 7, 47] .L) .L))))))))))))) (.W 487 [3] (.B 487 (.W 973 [3, 7, 19] (.W 1945 [3, 5, 7]
  (.W 3889 [3, 5, 23] .L))) (.W 973 [3, 7, 19] (.W 1945 [3, 5] (.W 1951 [] (.B 1951 (.W 3901 [3, 5, 23] .L)
  (.W 2683 [3, 23] (.B 2683 .L .L))))))))))) (.W 313 [3, 5] (.W 487 [3] (.B 487 (.W 631 [7] (.B 631 (.W 1261
  [3, 7, 19] (.W 2521 [3, 13, 23] .L)) (.W 1261 [3, 7, 19] .L))) (.W 631 [7] (.B 631 (.W 1261 [3, 19] .L) (.W
  1261 [3, 19] .L)))))))))) (.W 109 [3] (.B 109 (.W 127 [11] (.B 127 (.W 253 [3, 7] (.W 487 [3, 11] (.B 487
  (.W 973 [3, 7, 13] (.W 1945 [3, 5, 7] (.W 3889 [3, 11, 23] .L))) (.W 973 [3, 7, 13] (.W 1945 [3, 5] .L)))))
  (.W 253 [3, 7] (.W 487 [3] (.B 487 (.W 973 [7, 13] .L) (.W 973 [7, 13] .L)))))) (.W 127 [11] (.B 127 (.W
  253 [3, 5] (.W 439 [3, 11] (.B 439 (.W 487 [] (.B 487 (.W 877 [3, 7] (.B 877 (.W 1753 [3, 5, 7] .L) .L))
  (.W 877 [3, 7] (.B 877 .L .L)))) (.W 487 [] (.B 487 (.W 973 [3, 7, 19] .L) (.W 973 [3, 7, 19] .L)))))) (.W
  253 [3, 5] (.W 439 [3, 11] (.B 439 .L .L))))))))) (.W 79 [3] (.B 79 (.W 127 [3] (.B 127 (.W 157 [] (.B 157
  (.W 313 [3, 5, 11, 13] (.W 313 [] (.B 313 (.W 625 [3, 7] (.W 991 [3, 5, 19] (.B 991 (.W 1981 [3, 5] .L) (.W
  1981 [3, 5, 29] .L)))) (.W 625 [3, 7] (.W 991 [3, 19] (.B 991 (.W 1981 [3, 5] .L) .L)))))) (.W 313 [3, 5,
  11, 13] (.W 625 [3, 7] .L)))) (.W 157 [] (.B 157 (.W 313 [3, 5, 13] (.W 313 [] (.B 313 (.W 625 [3, 7] .L)
  (.W 625 [3, 7] .L)))) (.W 313 [3, 5, 13] (.W 625 [3, 7] .L)))))) (.W 109 [3] (.B 109 (.W 127 [3] (.B 127
  (.W 253 [7, 13] (.W 505 [3, 11] .L)) (.W 253 [7, 13] (.W 505 [3] .L)))) (.W 127 [3] (.B 127 (.W 253 [3, 5,
  13] (.W 439 [3, 11] (.B 439 .L .L))) (.W 253 [3, 5, 13] .L))))))))))) (.W 43 [3] (.B 43 (.W 79 [3] (.B 79
  (.W 127 [5] (.B 127 (.W 157 [] (.B 157 (.W 313 [3, 11] (.W 313 [] (.B 313 (.W 625 [3, 7] .L) (.W 625 [3, 7]
  .L)))) (.W 313 [3, 11] (.W 625 [3, 7] .L)))) (.W 157 [] (.B 157 (.W 313 [3] .L) (.W 313 [3] .L))))) (.W 127
  [5] (.B 127 (.W 253 [3] .L) (.W 253 [3] .L))))) (.W 79 [3] (.B 79 (.W 127 [3] (.B 127 (.W 157 [] (.B 157
  (.W 313 [3, 5, 11] .L) (.W 313 [3, 5, 11] .L))) (.W 157 [] (.B 157 .L .L)))) (.W 109 [3] (.B 109 .L (.W 127
  [] (.B 127 (.W 253 [3, 5] .L) .L)))))))))))) (.W 19 [3] (.B 19 (.W 23 [] (.B 23 (.W 31 [] (.B 31 (.W 37 []
  (.B 37 (.W 61 [3] (.B 61 .U (.W 73 [3] (.B 73 .U (.W 127 [3, 7] (.B 127 .U (.W 253 [3, 13] (.W 367 [3, 5]
  (.B 367 (.W 733 [3, 7] (.W 733 [] (.B 733 (.W 991 [] (.B 991 (.W 1981 [3, 5, 7] (.W 3961 [3, 7, 23] (.W
  7921 [3, 5, 11] (.W 7927 [] (.B 7927 (.W 8191 [] (.B 8191 (.W 16381 [3, 83] .L) (.W 16381 [3, 83] .L))) (.W
  8191 [] (.B 8191 (.W 16381 [3] .L) .L))))))) (.W 1981 [3, 5, 7] (.W 2293 [3, 23] (.B 2293 (.W 4585 [3] .L)
  (.W 3967 [3] (.B 3967 (.W 7933 [3, 5, 11] .L) (.W 7933 [3, 5, 11] .L)))))))) (.W 991 [] (.B 991 (.W 1981
  [3, 7] (.W 3961 [3, 5, 7, 23] .L)) (.W 1981 [3, 7] (.W 2293 [3, 23] (.B 2293 (.W 4585 [3, 5] .L) (.W 3967
  [3, 5] (.B 3967 .L .L)))))))))) (.W 733 [3, 7] (.W 991 [3] (.B 991 (.W 1471 [3, 7] (.B 1471 (.W 2941 [3, 7,
  23] .L) (.W 2941 [3, 7, 23] .L))) (.W 1471 [3, 7] (.B 1471 (.W 2293 [3, 23] (.B 2293 .L .L)) (.W 2293 [3,
  23] (.B 2293 .L .L)))))))))))))))) (.W 61 [3] (.B 61 (.W 121 [3, 7] (.W 127 [11] (.B 127 (.W 151 [] (.B 151
  (.W 301 [3, 11] (.W 367 [7] (.B 367 .U (.W 487 [] (.B 487 (.W 973 [3, 7] (.W 1471 [3, 5, 7, 17] (.B 1471 .U
  (.W 2941 [3, 23] (.W 4831 [3, 5, 17] (.B 4831 (.W 8191 [3, 7] (.B 8191 .U (.W 9661 [] (.B 9661 .U (.W 15583
  [3, 7] (.B 15583 .U (.W 31165 [3, 5, 11] (.W 62329 [3, 5, 7, 11] (.W 94207 [3, 5, 7] (.B 94207 (.W 131071
  [3, 7] (.B 131071 (.W 154591 [] (.B 154591 (.W 309181 [3, 5, 11, 23, 29] (.W 524287 [3, 11, 41] (.B 524287
  (.W 1048573 [3, 5, 13, 17] (.W 1048573 [] (.B 1048573 (.W 1236727 [3] (.B 1236727 (.W 2473453 [3, 5, 7, 37]
  .L) .L)) (.W 1236727 [3] (.B 1236727 .L .L))))) (.W 1048573 [3, 5, 13, 17] .L)))) (.W 309181 [3, 5, 11, 23,
  29] (.W 524287 [3, 11] (.B 524287 (.W 1048573 [3, 5, 13, 17, 29] .L) (.W 1048573 [3, 5, 13, 17, 29]
  .L)))))) (.W 154591 [] (.B 154591 (.W 309181 [3, 5, 23, 29] (.W 524287 [3, 11, 41] (.B 524287 (.W 1048573
  [3, 5, 17] .L) .L))) (.W 309181 [3, 5, 23, 29] (.W 524287 [3, 11] (.B 524287 .L .L))))))) (.W 131071 [3, 7]
  (.B 131071 (.W 154591 [] (.B 154591 (.W 309181 [3, 5, 11, 23, 71] (.W 524287 [3, 7, 11, 41] (.B 524287 (.W
  1048573 [3, 5, 7, 13, 17] .L) (.W 1048573 [3, 5, 7, 13, 17] .L)))) (.W 309181 [3, 5, 11, 23, 71] (.W 524287
  [3, 7, 11] (.B 524287 .L .L))))) (.W 154591 [] (.B 154591 (.W 309181 [3, 5, 23, 71] (.W 524287 [3, 7, 11,
  41] (.B 524287 .L .L))) (.W 309181 [3, 5, 23, 71] .L))))))))))))))) (.W 8191 [3, 7] (.B 8191 (.W 15583 [3,
  7, 29] (.B 15583 (.W 16381 [5] (.B 16381 (.W 32761 [3, 5, 7, 11] (.W 65521 [3, 5, 7, 181] (.W 94207 [3, 13]
  (.B 94207 .U (.W 131071 [3, 7] (.B 131071 .U (.W 262141 [3, 5, 7, 71] (.W 524281 [3, 5, 7, 17, 19] (.W
  524287 [] (.B 524287 .U (.W 889087 [3, 5, 23] (.B 889087 .U (.W 1778173 [3, 5, 7, 17, 19] (.W 1994623 [3]
  (.B 1994623 .U (.W 2991103 [3, 5, 7, 233] (.B 2991103 (.W 5982205 [3, 5, 7, 23] (.W 11964409 [3, 5, 7, 47]
  (.W 18824263 [3] (.B 18824263 (.W 23928823 [] (.B 23928823 (.W 33548287 [] (.B 33548287 (.W 67096573 [5,
  31] (.W 134193145 [3, 397] (.W 268386289 [3, 7, 11, 401] (.W 536772577 [3, 5] (.W 1073545153 [3, 5, 233]
  (.W 2147090305 [3, 1483] .L)))))) (.W 67096573 [5, 31] (.W 134193145 [3] (.W 268386289 [7, 11, 401, 1381]
  (.W 536772577 [3] .L)))))) (.W 33548287 [] (.B 33548287 (.W 67096573 [3, 5, 31] (.W 134193145 [3, 5, 397]
  (.W 268386289 [3, 7, 11] .L))) (.W 67096573 [3, 5, 31] (.W 134193145 [3, 5] .L)))))) (.W 19788247 [] (.B
  19788247 (.W 23928823 [] (.B 23928823 (.W 47857645 [11, 31, 139] (.W 95715289 [3, 5] (.W 191430577 [3, 5,
  7] (.W 382861153 [3, 401] .L)))) (.W 47857645 [11, 31, 139] (.W 95715289 [3] (.W 191430577 [5, 7] .L)))))
  (.W 23928823 [11] (.B 23928823 (.W 33548287 [139] (.B 33548287 (.W 67096573 [3, 5, 31] (.W 134193145 [3, 5,
  7, 397] (.W 268386289 [3, 7, 401] .L))) (.W 67096573 [3, 5, 31] (.W 79152991 [3, 5] (.B 79152991 (.W
  158305981 [3, 5, 7] .L) (.W 158305981 [3, 5, 7, 1381] .L)))))) (.W 33548287 [139] (.B 33548287 (.W 67096573
  [3, 31] (.W 134193145 [3, 5, 7, 397] .L)) (.W 67096573 [3, 31] (.W 79152991 [3, 5] (.B 79152991 (.W
  158305981 [5, 7] .L) (.W 158305981 [3, 5, 7, 1381] .L)))))))))))))) (.W 5982205 [3, 5, 7, 23, 31, 97, 113,
  1249] (.W 11964409 [3, 5, 7, 47, 59, 103, 157] (.W 18824263 [3, 5, 7, 113] (.B 18824263 (.W 33548287 [3, 7,
  67] (.B 33548287 .L .L)) (.W 19788247 [3] (.B 19788247 (.W 39576493 [3, 5, 7, 31, 139] .L) (.W 33548287 [3,
  5, 7, 11, 67, 139] (.B 33548287 .L .L))))))))))))))))))))))))) (.W 32761 [3, 5, 7, 11] (.W 65521 [3, 5, 7,
  181] (.W 94207 [3, 7, 13] (.B 94207 (.W 131071 [3, 7] (.B 131071 (.W 262111 [3, 5, 29] (.B 262111 (.W
  524221 [3, 5, 11, 17] .L) (.W 524221 [3, 5, 11, 17] .L))) (.W 262111 [3, 5, 29] (.B 262111 (.W 524221 [3,
  5, 17] .L) (.W 524221 [3, 5, 17] .L))))) (.W 131071 [3, 7] (.B 131071 (.W 262111 [3, 5, 7, 71] (.B 262111
  (.W 524221 [3, 5, 7, 11, 17] .L) (.W 524221 [3, 5, 7, 11, 17] .L))) (.W 262111 [3, 5, 7, 71] (.B 262111 .L
  .L)))))))))) (.W 16381 [5] (.B 16381 (.W 32761 [3, 7, 11] (.W 65521 [3, 5, 7, 11, 181] (.W 94207 [3, 13]
  (.B 94207 (.W 131071 [3, 7] (.B 131071 (.W 147073 [] (.B 147073 (.W 294145 [3, 5, 11, 29] (.W 524287 [3, 5,
  19] (.B 524287 .L .L))) (.W 294145 [3, 5, 11, 23, 29] (.W 524287 [3, 11, 17, 19] (.B 524287 .L .L))))) (.W
  147073 [] (.B 147073 (.W 294145 [3, 5, 29] .L) (.W 294145 [3, 5, 23, 29] .L))))) (.W 131071 [3, 7] (.B
  131071 (.W 147073 [] (.B 147073 (.W 294145 [3, 5, 11, 71] .L) (.W 294145 [3, 5, 7, 11, 23, 71] .L))) (.W
  147073 [] (.B 147073 (.W 294145 [3, 5, 71] .L) (.W 294145 [3, 5, 7, 23, 71] .L))))))))) (.W 32761 [3, 7,
  11] (.W 65521 [3, 5, 7, 11, 181] (.W 94207 [3, 7, 13] (.B 94207 (.W 131071 [3, 7] (.B 131071 (.W 147073 []
  (.B 147073 .L (.W 262111 [3, 5, 23, 29] (.B 262111 .L .L)))) .L)) (.W 131071 [3, 7] (.B 131071 (.W 147073
  [] (.B 147073 .L .L)) .L)))))))))) (.W 15583 [3, 7, 29] (.B 15583 (.W 31165 [3, 5, 7, 11] (.W 62329 [3, 5,
  7, 181] (.W 94207 [3, 7, 13] (.B 94207 .L .L)))) (.W 31165 [3, 5, 7, 11] (.W 62329 [3, 5, 7, 11, 181]
  .L)))))))))))) (.W 973 [3, 7] (.W 1471 [3, 5, 17] (.B 1471 (.W 1951 [] (.B 1951 (.W 3901 [3, 17, 23] (.W
  4831 [3, 17, 47] (.B 4831 (.W 8191 [3] (.B 8191 (.W 9661 [] (.B 9661 (.W 15607 [7] (.B 15607 (.W 16381 [5]
  (.B 16381 (.W 32761 [3, 7, 139] .L) (.W 32761 [3, 7, 139] .L))) (.W 16381 [5] (.B 16381 (.W 32761 [3, 139]
  .L) (.W 32761 [3, 139] .L))))) (.W 15607 [7] (.B 15607 (.W 16381 [5] (.B 16381 (.W 32761 [3, 7] .L) (.W
  32761 [3, 7] .L))) (.W 16381 [5] (.B 16381 (.W 32761 [3] .L) (.W 32761 [3] .L))))))) (.W 9661 [] (.B 9661
  (.W 15607 [7] (.B 15607 (.W 31213 [3, 5, 139] .L) .L)) (.W 15607 [7] (.B 15607 .L .L)))))) (.W 8191 [3] (.B
  8191 (.W 15607 [3, 7] (.B 15607 .L .L)) (.W 15607 [3, 7] (.B 15607 .L .L))))))) (.W 3901 [3, 17, 23] (.W
  4831 [3, 17] (.B 4831 (.W 8191 [3, 37] (.B 8191 (.W 9661 [] (.B 9661 (.W 15493 [7] (.B 15493 .L .L)) (.W
  15493 [7] (.B 15493 .L .L)))) (.W 9661 [] (.B 9661 .L .L)))) (.W 8191 [3, 37] (.B 8191 (.W 15493 [3, 7] (.B
  15493 .L .L)) .L))))))) (.W 1951 [] (.B 1951 (.W 3901 [3, 23] (.W 4831 [3, 17, 47] (.B 4831 (.W 8191 [3, 7]
  (.B 8191 (.W 9661 [] (.B 9661 (.W 15607 [3, 7] (.B 15607 .L .L)) .L)) .L)) (.W 8191 [3, 7] (.B 8191 (.W
  15607 [3, 7, 29] (.B 15607 .L .L)) .L))))) (.W 3901 [3, 23] (.W 4831 [3, 17] (.B 4831 (.W 8191 [3, 7, 31,
  37] (.B 8191 .L .L)) (.W 8191 [3, 7, 31, 37] (.B 8191 .L .L))))))))))))))) (.W 301 [3, 11] (.W 367 [3] (.B
  367 (.W 487 [] (.B 487 (.W 607 [3, 7] (.B 607 (.W 733 [] (.B 733 (.W 1213 [3, 5, 7] (.B 1213 (.W 2425 [3,
  5, 23] (.W 4849 [3, 5, 17] (.W 8191 [3, 11] (.B 8191 (.W 15583 [3, 31] (.B 15583 (.W 16381 [5] (.B 16381
  (.W 32761 [3, 5] (.W 65521 [3, 5, 7, 181] (.W 131041 [3, 7, 17] (.W 131071 [7] (.B 131071 (.W 262141 [3, 5,
  19, 139] (.W 308101 [3, 11] (.B 308101 (.W 524287 [3, 5, 19] (.B 524287 .L .L)) (.W 524287 [3, 5, 19] (.B
  524287 .L .L))))) (.W 262141 [3, 5, 19, 139] (.W 308101 [3] (.B 308101 .L .L)))))))) (.W 32761 [3, 5] (.W
  65521 [3, 5, 7] (.W 131041 [3, 7, 17] .L))))) (.W 16381 [5] (.B 16381 (.W 32761 [3, 5] (.W 65521 [3, 5, 7,
  181] (.W 131041 [3, 7, 17] .L))) (.W 32761 [3, 5] (.W 65521 [3, 5, 7] (.W 131041 [3, 7, 17] .L))))))) (.W
  15583 [3, 31] (.B 15583 (.W 31165 [3, 5] (.W 62329 [3, 5, 7] .L)) (.W 31165 [3, 5] (.W 62329 [3, 5, 7]
  .L)))))))) (.W 2425 [3, 5, 23] (.W 4849 [3, 5, 17] (.W 8191 [3, 5, 11] (.B 8191 (.W 15583 [3] (.B 15583 .L
  .L)) (.W 15583 [3] (.B 15583 .L .L)))))))) (.W 1213 [3, 5, 7] (.B 1213 (.W 2425 [3, 23] (.W 4849 [3, 5, 17]
  (.W 8191 [3] (.B 8191 (.W 11743 [31] (.B 11743 .L .L)) .L)))) (.W 2425 [3, 23] (.W 4849 [3, 5, 17] .L))))))
  (.W 733 [] (.B 733 (.W 1465 [3, 5, 7] (.W 2929 [3, 5, 11, 23] (.W 5857 [3, 5, 17] .L))) (.W 1465 [3, 5, 7]
  (.W 2929 [3, 11, 23] .L)))))) (.W 607 [3, 7] (.B 607 (.W 733 [] (.B 733 (.W 1213 [3, 5] (.B 1213 (.W 1951
  [5] (.B 1951 (.W 3901 [3, 5, 23] (.W 7801 [3, 11, 17, 47] .L)) (.W 3901 [3, 5, 23] (.W 7801 [3, 11, 17]
  .L)))) (.W 1951 [5] (.B 1951 (.W 3901 [3, 23] (.W 7801 [3, 5, 11, 17, 47] .L)) (.W 3901 [3, 23] .L))))) (.W
  1213 [3, 5] (.B 1213 (.W 1951 [3] (.B 1951 (.W 3901 [3, 5, 23] .L) (.W 3901 [3, 5, 23] .L))) (.W 1951 [3]
  (.B 1951 (.W 3901 [3, 5, 23] .L) (.W 3901 [3, 5, 23] .L))))))) (.W 733 [] (.B 733 (.W 1465 [3, 5] (.W 1951
  [5] (.B 1951 (.W 3901 [3, 11, 23] .L) (.W 3901 [3, 7, 11, 23] .L)))) (.W 1465 [3, 5] (.W 1951 [3] (.B 1951
  (.W 3901 [3, 5, 11, 23] .L) .L))))))))) (.W 487 [] (.B 487 (.W 607 [3, 7] (.B 607 (.W 1213 [3, 5, 7] (.W
  1213 [] (.B 1213 (.W 1471 [] (.B 1471 (.W 2941 [3, 5, 23] (.W 5881 [3, 5, 17] .L)) (.W 2941 [3, 5, 23]
  .L))) (.W 1471 [] (.B 1471 (.W 2941 [3, 23] .L) (.W 2941 [3, 23] .L)))))) (.W 1213 [3, 5, 7] (.W 1471 [3]
  (.B 1471 (.W 2941 [3, 11, 23] .L) (.W 1747 [] (.B 1747 .L (.W 3493 [3, 11, 23] .L)))))))) (.W 607 [3, 7]
  (.B 607 (.W 1213 [3, 5] (.W 1213 [] (.B 1213 (.W 1471 [] (.B 1471 (.W 1951 [] (.B 1951 (.W 3901 [3, 5, 17,
  23] .L) (.W 3901 [3, 5, 17, 23] .L))) (.W 1951 [] (.B 1951 (.W 3901 [3, 5, 23] .L) .L)))) (.W 1471 [] (.B
  1471 (.W 1951 [] (.B 1951 (.W 3901 [3, 17, 23] .L) .L)) (.W 1951 [] (.B 1951 .L .L))))))) (.W 1213 [3, 5]
  (.W 1471 [3] (.B 1471 .L .L)))))))))))) (.W 151 [] (.B 151 (.W 301 [3] (.W 367 [7] (.B 367 (.W 487 [] (.B
  487 (.W 733 [3, 7] (.B 733 (.W 1465 [3, 7, 17] (.W 2929 [3, 5, 23] .L)) (.W 1465 [3, 7, 17] (.W 2929 [3,
  23] .L)))) (.W 733 [3, 7] (.B 733 (.W 1465 [3, 17] (.W 1951 [5] (.B 1951 .L .L))) (.W 1465 [3, 17] .L)))))
  (.W 487 [] (.B 487 (.W 973 [3, 7] (.W 1471 [3, 7, 17] (.B 1471 .L .L))) (.W 973 [3, 7] (.W 1471 [3, 17] (.B
  1471 .L .L)))))))) (.W 301 [3] (.W 367 [3] (.B 367 (.W 487 [] (.B 487 (.W 607 [7] (.B 607 (.W 733 [] (.B
  733 (.W 1213 [3, 7] (.B 1213 (.W 2425 [3, 5, 23] .L) .L)) (.W 1213 [3, 7] (.B 1213 .L .L)))) (.W 733 [] (.B
  733 (.W 1465 [3, 7] .L) (.W 1465 [3, 7] .L))))) (.W 607 [7] (.B 607 (.W 733 [] (.B 733 (.W 1213 [3] (.B
  1213 .L .L)) (.W 1213 [3] (.B 1213 .L .L)))) (.W 733 [] (.B 733 (.W 1465 [3] .L) .L)))))) (.W 487 [] (.B
  487 (.W 607 [7] (.B 607 (.W 1213 [3, 7] .L) (.W 1213 [3, 7] .L))) (.W 607 [7] (.B 607 (.W 1213 [3] .L)
  .L)))))))))))) (.W 121 [3, 7] (.W 127 [3] (.B 127 (.W 151 [] (.B 151 (.W 301 [3, 11, 13] (.W 367 [7] (.B
  367 (.W 733 [3, 7] (.W 733 [] (.B 733 (.W 991 [] (.B 991 .L .L)) (.W 991 [] (.B 991 .L .L))))) (.W 733 [3,
  7] .L)))) (.W 301 [3, 11, 13] (.W 367 [3] (.B 367 (.W 607 [3, 7] (.B 607 .L .L)) (.W 607 [3, 7] (.B 607 .L
  .L))))))) (.W 151 [] (.B 151 (.W 301 [3, 13] (.W 367 [7] (.B 367 (.W 733 [3, 7] .L) (.W 733 [3, 7] .L))))
  (.W 301 [3, 13] (.W 367 [3] (.B 367 .L .L)))))))))))) (.W 37 [] (.B 37 (.W 73 [3] (.W 73 [] (.B 73 (.W 127
  [7] (.B 127 (.W 253 [3, 5] (.W 367 [3, 11] (.B 367 (.W 733 [3, 7, 11] .L) (.W 733 [3, 7, 11] .L)))) (.W 253
  [3, 5] (.W 367 [3] (.B 367 (.W 733 [7, 11] .L) .L))))) (.W 127 [7] (.B 127 (.W 253 [3] (.W 367 [3, 5, 11]
  (.B 367 .L .L))) (.W 253 [3] .L)))))) (.W 73 [3] (.W 127 [3, 7] (.B 127 (.W 151 [] (.B 151 (.W 301 [3, 11]
  .L) (.W 301 [3, 11] .L))) .L))))))) (.W 31 [] (.B 31 (.W 37 [] (.B 37 (.W 47 [] (.B 47 (.W 61 [] (.B 61 (.W
  73 [3] (.B 73 .U (.W 127 [3, 11] (.B 127 (.W 253 [3, 11] (.W 487 [3, 5, 11] (.B 487 (.W 751 [3, 7] (.B 751
  (.W 1501 [3, 5, 7] (.W 3001 [3, 19, 23] (.W 6001 [3, 5, 17] (.W 6007 [] (.B 6007 (.W 8191 [3] (.B 8191 (.W
  9397 [] (.B 9397 .U (.W 15583 [3, 41] (.B 15583 (.W 16381 [5] (.B 16381 .U (.W 32761 [3, 5, 19] (.W 37591
  [3, 7] (.B 37591 .U (.W 75181 [3, 5, 7] (.W 131071 [3, 5, 7] (.B 131071 .U (.W 262111 [3, 5, 7, 19] (.B
  262111 .U (.W 444517 [3, 47] (.B 444517 (.W 524287 [3, 5] (.B 524287 .U (.W 1048447 [3, 17, 673] (.B
  1048447 .U (.W 1994623 [3] (.B 1994623 (.W 3989245 [3, 5, 7, 71] (.W 7978489 [3, 5, 7] (.W 15956977 [3, 5,
  47, 241] (.W 31913953 [3, 7, 113, 1531] (.W 63827905 [3, 5, 31, 887] .L))))) (.W 3989245 [3, 5, 7, 71,
  1249] (.W 7978489 [3, 5, 7] (.W 15956977 [3, 5, 7, 47, 241] .L))))))))) (.W 524287 [3, 5] (.B 524287 (.W
  1048447 [3, 5, 11, 13, 17] (.B 1048447 (.W 1048573 [] (.B 1048573 .U (.W 1778071 [3, 5, 11] (.B 1778071 .U
  (.W 1994623 [] (.B 1994623 .U (.W 2096893 [3] (.B 2096893 .U (.W 4193785 [3, 5, 7, 11, 1249] (.W 8387569
  [3, 5, 7, 43] (.W 16775137 [3, 5, 7, 47, 113] (.W 16777183 [3] (.B 16777183 (.W 24412447 [3, 5, 7] (.B
  24412447 (.W 48824893 [3, 5, 29, 31, 139] (.W 77585077 [3, 13, 317] (.B 77585077 (.W 155170153 [3, 5, 7,
  19] (.W 310340305 [3, 5, 61] .L)) (.W 155170153 [3, 5, 7, 19, 61] (.W 310340305 [3, 5, 13] .L))))) (.W
  48824893 [3, 5, 29, 31, 59, 139, 211] (.W 49209343 [3] (.B 49209343 (.W 77585077 [3, 5, 31, 317] (.B
  77585077 (.W 155170153 [3, 5, 7, 19] (.W 310340305 [3, 7, 61, 137] .L)) (.W 153976831 [3, 5, 7, 17, 19, 61]
  (.B 153976831 (.W 307953661 [3] .L) (.W 307953661 [3, 7, 13, 41, 137] .L))))) (.W 77585077 [3, 5, 31, 317]
  (.B 77585077 (.W 97649791 [] (.B 97649791 (.W 195299581 [5, 7, 19, 61] .L) (.W 195299581 [3, 5, 7, 19, 61,
  12437] .L))) (.W 97649791 [61] (.B 97649791 (.W 195299581 [3, 5, 7, 19] .L) (.W 153976831 [3, 5, 7, 17, 19,
  41] (.B 153976831 .L (.W 307953661 [3, 5, 7, 13, 41, 137, 1759, 12437] .L)))))))))))) (.W 24412447 [3, 5,
  7] (.B 24412447 (.W 48824893 [3, 29, 31, 73, 139] (.W 77585077 [3, 5, 13, 317] (.B 77585077 (.W 155170153
  [3, 5, 7] .L) (.W 155170153 [3, 5, 7, 61] .L)))) (.W 48824893 [3, 29, 31, 59, 73, 139, 211] (.W 49209343
  [3] (.B 49209343 (.W 77585077 [3, 5, 31, 317] (.B 77585077 (.W 155170153 [3, 5, 7, 109] .L) (.W 153976831
  [3, 5, 7, 17, 61, 109] (.B 153976831 .L .L)))) (.W 77585077 [3, 5, 31, 317] (.B 77585077 (.W 97649791 []
  (.B 97649791 .L .L)) (.W 97649791 [3, 61] (.B 97649791 .L (.W 153976831 [3, 5, 7, 17, 41, 109] (.B
  153976831 .L .L)))))))))))))))))))))))) (.W 1048573 [] (.B 1048573 (.W 1778071 [3, 5, 11] (.B 1778071 .U
  (.W 1994623 [] (.B 1994623 .U (.W 3989245 [3, 5, 7, 11, 71, 1249] (.W 7978489 [3, 5, 7, 43] (.W 15956977
  [3, 5, 7, 47] (.W 24412447 [3, 5, 7, 113, 1531] (.B 24412447 (.W 48824893 [3, 5, 31, 139] (.W 97649785 [3,
  11, 13, 29, 61, 317] (.W 155170303 [3, 5, 7, 13] (.B 155170303 .L .L)))) (.W 48824893 [3, 5, 31, 59, 139,
  211, 887] (.W 49209343 [3] (.B 49209343 (.W 98418685 [3, 5, 11, 29, 31, 41, 61, 317] (.W 153976831 [3, 5,
  7, 13, 17] (.B 153976831 .L .L))) (.W 97649791 [3, 5, 11, 29, 31, 41, 61, 317] (.B 97649791 .L (.W
  153976831 [3, 5, 7, 13, 17, 23, 41] (.B 153976831 .L .L)))))))))))))))) (.W 1778071 [3, 5, 11] (.B 1778071
  (.W 1994623 [] (.B 1994623 (.W 3989245 [3, 7, 53, 71] (.W 7978489 [3, 5, 7] (.W 15956977 [3, 5, 7, 47] (.W
  16777183 [3, 7, 113, 1531] (.B 16777183 .U (.W 33554365 [3, 887] (.W 56898271 [3, 31] (.B 56898271 (.W
  113796541 [3, 5, 11] (.W 227593081 [3, 5, 7, 47, 109] (.W 255311743 [3] (.B 255311743 (.W 510623485 [3, 7,
  457] .L) (.W 510623485 [3, 7, 83, 457] .L))))) (.W 113796541 [3, 5, 11] (.W 227593081 [3, 5, 7, 109] (.W
  227593087 [] (.B 227593087 (.W 255311743 [] (.B 255311743 (.W 510623485 [3, 7, 13] .L) (.W 510623485 [3, 7,
  13, 83] .L))) (.W 255311743 [] (.B 255311743 (.W 510623485 [3, 7, 997] .L) (.W 510623485 [3, 7, 83, 997]
  .L))))))))))))))) (.W 3989245 [3, 7, 53, 71, 1249] (.W 7978489 [3, 5, 7] (.W 15956977 [3, 5, 7, 47] (.W
  16777183 [3, 113, 1531] (.B 16777183 (.W 33554365 [3, 139, 887] .L) (.W 33554365 [3, 139, 887] .L))))))))
  (.W 1994623 [] (.B 1994623 (.W 3989245 [3, 5, 7, 11, 71] (.W 7978489 [3, 5, 7] (.W 15956977 [3, 5, 7, 47]
  (.W 16777183 [3, 7, 113, 1531] (.B 16777183 (.W 24412447 [3, 5] (.B 24412447 (.W 48824893 [3, 5, 31] .L)
  (.W 48824893 [3, 5, 31, 59, 211, 887] .L))) (.W 24412447 [3, 5] (.B 24412447 (.W 48824893 [3, 5, 31, 73]
  .L) (.W 48824893 [3, 5, 31, 59, 73, 211, 887] .L)))))))) (.W 3989245 [3, 5, 7, 11, 71, 1249] (.W 7978489
  [3, 5, 7, 43] (.W 15956977 [3, 5, 7, 47] .L))))))))))) (.W 1048447 [3, 5, 11, 13, 17] (.B 1048447 (.W
  1778071 [3, 5, 11] (.B 1778071 (.W 1994623 [] (.B 1994623 (.W 2096893 [3] (.B 2096893 (.W 4193785 [5, 7,
  53] (.W 8387569 [3, 5] (.W 16775137 [3, 7, 47, 113] (.W 33550273 [3, 7] .L)))) (.W 4193785 [5, 7, 53] (.W
  8387569 [3] (.W 16775137 [5, 7, 47, 113] .L))))) (.W 2096893 [3] (.B 2096893 (.W 4193785 [3, 5, 7, 53,
  1249] (.W 8387569 [3, 5] (.W 16775137 [3, 7, 47, 113] .L))) (.W 4193785 [3, 5, 7, 53, 1249] (.W 8387569 [3,
  5] .L)))))) (.W 1994623 [] (.B 1994623 (.W 2096893 [3] (.B 2096893 (.W 4193785 [3, 5, 7, 11] (.W 8387569
  [3, 5, 7] (.W 16775137 [3, 5, 7, 47, 113] .L))) (.W 4193785 [3, 5, 7, 11] (.W 8387569 [3, 7] (.W 16775137
  [3, 5, 7, 47, 113] .L))))) (.W 2096893 [3] (.B 2096893 (.W 4193785 [3, 5, 7, 11, 1249] (.W 8387569 [3, 5,
  7, 43] (.W 16775137 [3, 5, 7, 47, 113] .L))) (.W 4193785 [3, 5, 7, 11, 1249] (.W 8387569 [3, 5, 7, 43]
  .L)))))))) (.W 1778071 [3, 5, 11] (.B 1778071 (.W 1994623 [] (.B 1994623 (.W 3989245 [3, 7, 53, 71] (.W
  7978489 [3, 5, 7] .L)) (.W 3989245 [3, 7, 53, 71, 1249] (.W 7978489 [3, 5, 7] .L)))) (.W 1994623 [] (.B
  1994623 (.W 3989245 [3, 5, 7, 11, 71] (.W 7978489 [3, 5, 7] .L)) (.W 3989245 [3, 5, 7, 11, 71, 1249] (.W
  7978489 [3, 5, 7, 43] .L)))))))))))))))))))))) (.W 16381 [5] (.B 16381 (.W 32761 [3, 19] (.W 36037 [7, 181]
  (.B 36037 .U (.W 37591 [] (.B 37591 .U (.W 75181 [3, 5, 7] (.W 131071 [3, 5, 7] (.B 131071 .U (.W 262141
  [3, 5, 7, 19, 23] (.W 444517 [3, 47] (.B 444517 (.W 524287 [3, 11, 19] (.B 524287 (.W 1048573 [3, 5, 17,
  673] (.W 1048573 [] (.B 1048573 (.W 2097145 [3, 37, 233] (.W 4194289 [3, 5, 7, 113] (.W 8388577 [3, 7] (.W
  16777153 [3, 5, 7, 47, 113, 241] .L)))) (.W 2097145 [3, 37, 233] (.W 4194289 [3, 5, 7, 113] (.W 8388577 [3,
  5, 7] .L)))))) (.W 1048573 [3, 5, 17, 673] (.W 2097145 [3, 37, 233] (.W 4194289 [3, 5, 7, 113] .L))))) (.W
  524287 [3, 11, 19] (.B 524287 (.W 1048573 [3, 5, 13, 17, 29] (.W 1048573 [] (.B 1048573 (.W 1778071 [3, 5,
  11, 31] (.B 1778071 (.W 3556141 [3, 5, 7, 37, 233] (.W 7112281 [3, 5, 7, 53, 113] .L)) (.W 3556141 [3, 5,
  7, 11, 31, 37, 233] (.W 7112281 [3, 5, 7, 113] .L)))) (.W 1778071 [3, 5, 11, 31] (.B 1778071 (.W 3556141
  [3, 7, 37, 233] (.W 7112281 [3, 5, 7, 53, 113] .L)) (.W 3556141 [3, 7, 11, 31, 37, 233] (.W 7112281 [3, 5,
  7, 113] .L))))))) (.W 1048573 [3, 5, 13, 17, 29] (.W 1778071 [3, 5, 11, 31] (.B 1778071 (.W 3556141 [3, 7,
  37, 233] .L) (.W 3556141 [3, 7, 11, 31, 37, 233] .L))))))))))))))))) (.W 32761 [3, 19] (.W 36037 [3, 7] (.B
  36037 (.W 72073 [3, 5, 7] (.W 72073 [] (.B 72073 (.W 131071 [3] (.B 131071 (.W 262111 [5, 19] (.B 262111
  (.W 524221 [3, 11] (.W 524221 [] (.B 524221 (.W 524287 [3] (.B 524287 (.W 1048573 [5, 7, 13, 17] (.W
  1048573 [] (.B 1048573 (.W 2097145 [3, 11] .L) (.W 2097145 [3, 11] .L)))) (.W 1048573 [5, 7, 13, 17] (.W
  2097145 [3, 11] .L)))) (.W 524287 [3] (.B 524287 (.W 1048573 [3, 5, 7, 13, 17] (.W 1048573 [] (.B 1048573
  (.W 2097145 [3, 11, 13] .L) (.W 2097145 [3, 11, 13] .L)))) (.W 1048573 [3, 5, 7, 13, 17] .L)))))) (.W
  524221 [3, 11] (.W 524287 [3] (.B 524287 (.W 1048447 [5, 7, 17] (.B 1048447 (.W 1048573 [13] (.B 1048573
  (.W 2096893 [3, 11] (.B 2096893 .L .L)) (.W 2096893 [3, 11] (.B 2096893 .L .L)))) .L)) (.W 1048447 [5, 7,
  17] (.B 1048447 .L .L))))))) (.W 262111 [5, 19] (.B 262111 (.W 524221 [3] (.W 524221 [] (.B 524221 (.W
  524287 [] (.B 524287 (.W 1048573 [5, 7, 17] .L) (.W 1048573 [5, 7, 17] .L))) (.W 524287 [] (.B 524287 (.W
  1048573 [3, 5, 7, 17] .L) (.W 1048573 [3, 5, 7, 17] .L)))))) (.W 524221 [3] .L))))) (.W 131071 [3] (.B
  131071 (.W 262111 [3, 5, 19] (.B 262111 (.W 524221 [3, 5, 11] .L) (.W 524221 [3, 5, 11] .L))) (.W 262111
  [3, 5, 19] (.B 262111 (.W 524221 [3, 5] .L) (.W 524221 [3, 5] .L)))))))) (.W 37591 [] (.B 37591 (.W 75181
  [3, 5, 7] (.W 75181 [] (.B 75181 (.W 131071 [3] (.B 131071 (.W 262111 [19, 23, 53] (.B 262111 (.W 524221
  [3, 11] (.W 524221 [] (.B 524221 (.W 524287 [3] (.B 524287 (.W 1048573 [5, 7, 13, 17] (.W 1048573 [] (.B
  1048573 (.W 2097145 [3] .L) (.W 2097145 [3] .L)))) (.W 1048573 [5, 7, 13, 17] .L))) (.W 524287 [3] (.B
  524287 (.W 1048573 [3, 5, 7, 13] (.W 1048573 [] (.B 1048573 (.W 2097145 [3, 13] .L) (.W 2097145 [3, 13]
  .L)))) (.W 1048573 [3, 5, 7, 13] .L)))))) (.W 524221 [3, 11] (.W 524287 [3] (.B 524287 (.W 1048447 [5, 7]
  (.B 1048447 .L .L)) (.W 1048447 [5, 7] (.B 1048447 .L .L))))))) (.W 262111 [19, 23, 53] (.B 262111 (.W
  524221 [3] .L) (.W 524221 [3] .L))))) (.W 131071 [3] (.B 131071 (.W 262111 [3, 19, 23] (.B 262111 (.W
  524221 [3, 7, 11] .L) (.W 524221 [3, 7, 11] .L))) (.W 262111 [3, 19, 23] (.B 262111 (.W 524221 [3, 7] .L)
  (.W 524221 [3, 7] .L)))))))) (.W 75181 [3, 5, 7] (.W 131071 [3, 5, 7] (.B 131071 (.W 262111 [3, 5, 7, 19,
  23] (.B 262111 (.W 444517 [3, 11, 47] (.B 444517 .L .L)) (.W 444517 [3, 11, 47] (.B 444517 .L .L)))) (.W
  262111 [3, 5, 7, 19, 23] (.B 262111 .L .L)))))))))))))))) (.W 9397 [] (.B 9397 (.W 15583 [41] (.B 15583 (.W
  18793 [3] (.B 18793 .U (.W 37585 [3, 5, 7] (.W 75169 [3, 5] (.W 131071 [3, 5, 7] (.B 131071 (.W 262141 [3,
  19] (.W 524281 [3, 5, 11, 13] (.W 524287 [3] (.B 524287 (.W 1048573 [3, 5, 13] (.W 1048573 [] (.B 1048573
  (.W 1994623 [3, 5] (.B 1994623 .L .L)) (.W 1994623 [3, 5] (.B 1994623 .L .L))))) (.W 1048573 [3, 5, 13] (.W
  1994623 [3, 5] (.B 1994623 .L .L))))))) (.W 262141 [3, 19] (.W 524281 [3, 5, 13] (.W 524287 [] (.B 524287
  (.W 1048573 [3, 5] .L) (.W 1048573 [3, 5] .L))))))))))) (.W 18793 [3] (.B 18793 (.W 37585 [3, 7] (.W 75169
  [3, 5] (.W 131071 [3] (.B 131071 (.W 150343 [] (.B 150343 (.W 300685 [3, 11, 19, 23] (.W 524287 [3, 5] (.B
  524287 (.W 1048573 [3, 5, 13] .L) (.W 1048573 [3, 5, 13] .L)))) (.W 300685 [3, 11, 19, 23] (.W 524287 [3]
  (.B 524287 (.W 1048573 [5, 13] .L) (.W 1048573 [5, 13] .L)))))) (.W 150343 [] (.B 150343 (.W 300685 [3, 19,
  23] (.W 524287 [3, 5] (.B 524287 (.W 1048573 [3, 5] .L) .L))) (.W 300685 [3, 19, 23] (.W 524287 [3] (.B
  524287 .L .L))))))))) (.W 37585 [3, 7] (.W 75169 [3, 5] (.W 131071 [3, 5] (.B 131071 (.W 262141 [3, 19, 23]
  .L) .L)))))))) (.W 15583 [3, 41] (.B 15583 (.W 31165 [3, 5, 19] (.W 37591 [3, 5, 7] (.B 37591 (.W 75181 [3,
  5] (.W 75181 [] (.B 75181 (.W 131071 [3, 7] (.B 131071 (.W 262141 [3, 19, 53] .L) .L)) (.W 131071 [3, 7]
  (.B 131071 (.W 262141 [3, 19] .L) .L))))) (.W 75181 [3, 5, 7] (.W 131071 [3, 5, 7] (.B 131071 .L .L))))))
  (.W 31165 [3, 5, 19] (.W 36037 [3, 7] (.B 36037 (.W 72073 [3, 5, 7] .L) (.W 37591 [] (.B 37591 (.W 75181
  [3, 5] .L) (.W 75181 [3, 5, 7] .L)))))))))))) (.W 8191 [3] (.B 8191 (.W 9397 [] (.B 9397 (.W 15583 [3] (.B
  15583 (.W 16381 [] (.B 16381 (.W 18793 [3] (.B 18793 .U (.W 37585 [5, 7, 181] (.W 75169 [3] (.W 131071 [5,
  7, 97] (.B 131071 .U (.W 262141 [3] (.W 524281 [3, 5, 13, 19, 29] (.W 524287 [] (.B 524287 (.W 1048573 [3]
  (.W 1048573 [] (.B 1048573 .U (.W 1994623 [3, 5, 7] (.B 1994623 .U (.W 3989245 [3, 7, 233] (.W 4811263 [3,
  5] (.B 4811263 .U (.W 6152191 [] (.B 6152191 .U (.W 12304381 [3, 5, 7, 47] (.W 16777183 [3, 1307] (.B
  16777183 (.W 33548287 [3, 5, 11, 89, 139] (.B 33548287 (.W 67096573 [3, 5, 31] (.W 134193145 [3, 5, 7, 31,
  79, 397] (.W 268386289 [3, 7, 19, 569] (.W 536772577 [3, 5, 7, 19, 313] .L)))) (.W 67096573 [3, 5, 31] (.W
  134193145 [3, 5, 7, 31, 79, 2731] (.W 268386289 [3, 7, 19, 569, 1381] .L))))) (.W 33548287 [3, 5, 11, 89,
  139] (.B 33548287 (.W 67096573 [3, 5, 31] (.W 134193145 [3, 5, 7, 31, 79, 397] (.W 268386289 [3, 7, 569]
  .L))) (.W 67096573 [3, 5, 31] (.W 134193145 [3, 5, 7, 31, 79, 2731] .L))))))))))))))))) (.W 1048573 [3] (.W
  1994623 [3, 5, 7] (.B 1994623 (.W 3989245 [3, 7, 233] (.W 4811263 [3, 5] (.B 4811263 (.W 6152191 [] (.B
  6152191 (.W 12304381 [3, 5, 7, 47] .L) (.W 12304381 [3, 5, 7, 47] .L))) (.W 6152191 [] (.B 6152191 (.W
  12304381 [3, 7, 47] .L) (.W 12304381 [3, 7, 47] .L)))))) (.W 3989245 [3, 7, 233] (.W 4811263 [3] (.B
  4811263 (.W 6152191 [] (.B 6152191 (.W 12304381 [5, 7, 47] .L) (.W 12304381 [5, 7, 47] .L))) (.W 6152191 []
  (.B 6152191 (.W 12304381 [3, 5, 7, 47] .L) .L)))))))))))))))))) (.W 18793 [3] (.B 18793 (.W 37585 [3, 5, 7]
  (.W 75169 [3, 5, 7] (.W 131071 [3, 7, 97] (.B 131071 (.W 150343 [] (.B 150343 .U (.W 262111 [3] (.B 262111
  .U (.W 524221 [3, 5, 11, 29] (.W 524287 [3] (.B 524287 (.W 1048447 [3, 5] (.B 1048447 .U (.W 1048573 [13]
  (.B 1048573 .U (.W 1994623 [3, 7] (.B 1994623 .U (.W 3989245 [3, 7, 97] (.W 4194271 [3, 7] (.B 4194271 (.W
  6152191 [3, 5] (.B 6152191 .U (.W 12304381 [3, 5, 7, 47, 541] (.W 16777183 [3, 1531] (.B 16777183 (.W
  33554167 [3, 5, 89, 139] (.B 33554167 .U (.W 49211527 [3, 5, 31, 257] (.B 49211527 (.W 98423053 [3] (.W
  196846105 [5, 7, 19, 73, 229] (.W 393692209 [3] (.W 787384417 [5, 7, 13, 233, 16699] (.W 1574768833 [3] (.W
  2147483647 [5, 17, 31, 61] (.B 2147483647 (.W 4294967293 [3, 5, 47] (.W 8589934585 [3, 5, 43, 89, 9241]
  .L)) (.W 4294967293 [3, 5, 47] .L)))))))) (.W 98423053 [3, 11, 79] (.W 196846105 [3, 5, 7, 19, 181, 229]
  (.W 393692209 [3, 5, 7] (.W 787384417 [3, 5, 7, 13, 19, 233, 16699] .L)))))))) (.W 33554167 [3, 5, 89, 139]
  (.B 33554167 (.W 49211527 [3, 31, 257] (.B 49211527 (.W 98423053 [3, 5, 17] (.W 196846105 [3, 5, 7, 73] (.W
  393692209 [3, 5, 7] (.W 787384417 [3, 5, 7, 13, 233, 16699] .L)))) (.W 98423053 [3, 5, 11, 17, 79] (.W
  196846105 [3, 5, 7, 181] (.W 393692209 [3, 5, 7] .L))))) (.W 49211527 [3, 31, 257] (.B 49211527 (.W
  98423053 [3, 5] (.W 196846105 [3, 5, 7, 73, 229] (.W 393692209 [3, 7] .L))) (.W 98423053 [3, 5, 11, 79] (.W
  196846105 [3, 5, 7, 181, 229] .L))))))))))) (.W 6152191 [3, 5] (.B 6152191 (.W 12304381 [3, 5, 47] (.W
  16777183 [3, 19, 71, 1531] (.B 16777183 (.W 33554365 [3, 139] (.W 49217527 [5, 31, 257] (.B 49217527 (.W
  67108351 [3, 11] (.B 67108351 (.W 98435053 [3] (.B 98435053 (.W 196870105 [3, 5, 7, 19, 31] (.W 393740209
  [3, 5, 7] .L)) (.W 196870105 [3, 5, 7, 19, 31] (.W 393740209 [3, 5, 7] .L)))) (.W 98435053 [3] (.B 98435053
  (.W 196870105 [3, 5, 7, 19] (.W 393740209 [3, 5, 7, 11] .L)) (.W 196870105 [3, 5, 7, 19] (.W 393740209 [3,
  5, 7, 11] .L)))))) (.W 67108351 [3, 11] (.B 67108351 (.W 134216701 [3, 5] (.W 196870111 [5, 7, 19, 31] (.B
  196870111 (.W 393740221 [3, 5, 7] .L) .L))) (.W 134216701 [3, 5] (.W 196870111 [3, 5, 7, 19] (.B 196870111
  .L .L)))))))) (.W 33554365 [3, 139] (.W 49217527 [3, 31, 257] (.B 49217527 (.W 67108351 [3, 11] (.B
  67108351 (.W 98435053 [3, 5] (.B 98435053 (.W 196870105 [3, 5, 7, 31] .L) (.W 196870105 [3, 5, 7, 31] .L)))
  (.W 98435053 [3, 5] (.B 98435053 (.W 196870105 [3, 5, 7] .L) (.W 196870105 [3, 5, 7] .L))))) (.W 67108351
  [3, 11] (.B 67108351 (.W 134216701 [3, 5] .L) (.W 134216701 [3, 5] .L))))))))) (.W 12304381 [3, 5, 47, 541]
  (.W 16777183 [3, 71, 1531] (.B 16777183 (.W 33554365 [3, 5, 89, 139] (.W 49211527 [3, 5, 31, 257] (.B
  49211527 (.W 67108351 [3] (.B 67108351 .L .L)) (.W 67108351 [3, 11] (.B 67108351 .L .L))))) (.W 33554365
  [3, 5, 89, 139] (.W 49211527 [3, 31, 257] (.B 49211527 .L (.W 67108351 [3, 11] (.B 67108351 .L
  .L))))))))))))))))))) (.W 1048447 [3, 5] (.B 1048447 (.W 1994623 [3, 7, 13] (.B 1994623 (.W 2096893 [] (.B
  2096893 (.W 4193785 [3, 5, 7, 97] (.W 4194271 [5] (.B 4194271 (.W 6152191 [3] (.B 6152191 .U (.W 12304381
  [3, 5, 7, 47] (.W 24608761 [3, 7] (.W 33554167 [3, 5, 89] (.B 33554167 (.W 67108333 [3, 5, 31, 257] (.W
  134216665 [3, 7, 17, 181] (.W 255311743 [3, 5, 7] (.B 255311743 (.W 510623485 [3, 5, 13, 19] (.W 1021246969
  [3, 5, 233, 16699] .L)) (.W 510623485 [3, 5, 13, 19] .L))))) (.W 67108333 [3, 5, 31, 257] (.W 134216665 [3,
  7, 181] (.W 255311743 [3, 5, 7, 229] (.B 255311743 (.W 510623485 [3, 5, 13, 19] .L) .L)))))))))) (.W
  6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 47] (.W 24608761 [3, 7, 19, 71] (.W 49217521 [3, 31, 257] (.W
  49217527 [] (.B 49217527 (.W 67108351 [5] (.B 67108351 (.W 98435053 [3] (.B 98435053 (.W 196870105 [3, 5,
  7, 31] .L) (.W 196870105 [3, 5, 7, 31] .L))) (.W 98435053 [3] (.B 98435053 (.W 196870105 [3, 5, 7] .L) (.W
  196870105 [3, 5, 7] .L))))) (.W 67108351 [5] (.B 67108351 (.W 134216701 [3] .L) (.W 134216701 [3]
  .L)))))))) (.W 12304381 [3, 5, 47] (.W 24608761 [3, 7, 71] (.W 49217521 [3, 5, 31, 89, 257] .L)))))))) (.W
  4193785 [3, 5, 7, 97] (.W 4194271 [3] (.B 4194271 (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 7, 47]
  (.W 24608761 [3, 7, 19] (.W 33554167 [3, 29] (.B 33554167 (.W 49217527 [31, 257] (.B 49217527 .L .L)) (.W
  49217527 [31, 257] (.B 49217527 .L .L)))))) (.W 12304381 [3, 5, 7, 47] (.W 24608761 [3, 7] (.W 33554167 [3,
  5, 29, 89] (.B 33554167 .L .L)))))) (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 47] (.W 24608761 [3, 7,
  19, 71] .L)) (.W 12304381 [3, 5, 47] (.W 24608761 [3, 7, 71] .L))))))))) (.W 2096893 [] (.B 2096893 (.W
  4193785 [3, 7, 97] (.W 4194271 [5] (.B 4194271 (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 7, 47] (.W
  24608761 [3, 7, 19] (.W 33554167 [3, 139] (.B 33554167 (.W 49217527 [31, 257] (.B 49217527 .L .L)) (.W
  49217527 [31, 257] (.B 49217527 .L .L)))))) (.W 12304381 [3, 5, 7, 47] (.W 24608761 [3, 5, 7] (.W 33554167
  [3, 5, 89, 139] (.B 33554167 .L .L)))))) (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 47] (.W 24608761
  [3, 7, 19, 71] .L)) (.W 12304381 [3, 5, 47] (.W 24608761 [3, 5, 7, 71] .L))))))) (.W 4193785 [3, 7, 97] (.W
  4194271 [3] (.B 4194271 (.W 6152191 [3] (.B 6152191 (.W 12304381 [5, 7, 47] (.W 24608761 [3, 19] .L)) (.W
  12304381 [5, 7, 47] (.W 24608761 [3, 5] .L)))) (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 47] (.W
  24608761 [3, 19, 71] .L)) (.W 12304381 [3, 5, 47] .L)))))))))) (.W 1994623 [3, 7, 13] (.B 1994623 (.W
  3989245 [3, 7, 97] (.W 4194271 [5, 7] (.B 4194271 (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 7, 47]
  .L) (.W 12304381 [3, 5, 7, 47, 541] .L))) (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 47] .L) (.W
  12304381 [3, 5, 47, 541] .L)))))) (.W 3989245 [3, 7, 97] (.W 4194271 [3, 7] (.B 4194271 (.W 6152191 [3] (.B
  6152191 (.W 12304381 [3, 5, 7, 47] .L) (.W 12304381 [3, 5, 7, 47, 541] .L))) (.W 6152191 [3] (.B 6152191
  (.W 12304381 [3, 5, 47] .L) (.W 12304381 [3, 5, 47, 541] .L))))))))))))))))) (.W 150343 [] (.B 150343 (.W
  262111 [3] (.B 262111 .U (.W 524221 [3, 5, 29] (.W 524287 [3] (.B 524287 (.W 1048447 [3] (.B 1048447 (.W
  1048573 [] (.B 1048573 .U (.W 1202743 [3] (.B 1202743 .U (.W 1994623 [7] (.B 1994623 .U (.W 2096893 [] (.B
  2096893 .U (.W 4193785 [3, 7] (.W 6152191 [3, 5] (.B 6152191 (.W 12304381 [3, 5, 47] (.W 16777183 [3, 19]
  (.B 16777183 (.W 33554365 [3, 7, 29, 139] (.W 49217527 [3, 5, 31] (.B 49217527 (.W 98435053 [3, 5] (.W
  98435053 [] (.B 98435053 (.W 196870105 [3, 5, 7, 19] .L) (.W 196870105 [3, 5, 7, 19] .L)))) (.W 98435053
  [3, 5] (.W 196870105 [3, 5, 7, 19] .L))))) (.W 33554365 [3, 7, 29, 139] (.W 49217527 [3, 31] (.B 49217527
  (.W 98435053 [3, 5] .L) (.W 98435053 [3, 5] .L))))))) (.W 12304381 [3, 5, 47] (.W 16777183 [3] (.B 16777183
  (.W 33554365 [3, 5, 7, 29, 89, 139] (.W 67108729 [3, 5, 31] .L)) (.W 33554365 [3, 5, 7, 29, 89, 139] (.W
  67108729 [3, 31] .L)))))))))))))))) (.W 1048573 [] (.B 1048573 (.W 1202743 [3] (.B 1202743 .U (.W 1994623
  [7] (.B 1994623 .U (.W 3989245 [3, 5, 7] (.W 6152191 [3, 5, 7] (.B 6152191 (.W 12304381 [3, 5, 7, 47] (.W
  24608761 [3, 7, 19, 1531] (.W 49217521 [3, 5, 31, 139] (.W 49217527 [] (.B 49217527 (.W 98435053 [3, 5, 11]
  .L) (.W 98435053 [3, 5, 11] .L)))))) (.W 12304381 [3, 5, 7, 47, 541] (.W 24608761 [3, 5, 7, 1531] (.W
  49211527 [3, 5, 31, 89, 139] (.B 49211527 .L .L))))))))))) (.W 1202743 [3] (.B 1202743 (.W 1994623 [7] (.B
  1994623 .U (.W 3989245 [3, 5, 7] (.W 6152191 [3, 5, 7] (.B 6152191 (.W 9621943 [3, 5, 47] (.B 9621943 (.W
  16777183 [3, 19, 1531] (.B 16777183 (.W 33554365 [3, 5, 139] (.W 49217527 [3, 5, 31] (.B 49217527 (.W
  98435053 [3, 11, 211] (.W 98435053 [] (.B 98435053 (.W 196870105 [3, 5, 7, 19] .L) (.W 196870105 [3, 5, 7,
  19] .L)))) (.W 98435053 [3, 11, 211] .L)))) (.W 33554365 [3, 5, 139] (.W 49217527 [3, 31] (.B 49217527 (.W
  98435053 [3, 5, 11, 211] .L) (.W 98435053 [3, 5, 11, 211] .L)))))) (.W 16777183 [3, 19, 1531] (.B 16777183
  (.W 33554365 [3, 139] (.W 49217527 [5, 31] (.B 49217527 (.W 98435053 [3, 11] .L) (.W 98435053 [3, 11]
  .L)))) (.W 33554365 [3, 139] (.W 49217527 [3, 5, 31] (.B 49217527 .L .L))))))) (.W 9621943 [3, 5, 47] (.B
  9621943 (.W 16777183 [3, 541, 1531] (.B 16777183 (.W 33554365 [3, 5, 89, 139] (.W 49211527 [3, 5, 31] (.B
  49211527 .L .L))) (.W 33554365 [3, 5, 89, 139] (.W 49211527 [3, 31] (.B 49211527 .L .L))))) (.W 16777183
  [3, 541, 1531] (.B 16777183 (.W 33554365 [3, 5, 89, 139] (.W 49211527 [3, 5, 31] (.B 49211527 .L .L))) (.W
  33554365 [3, 5, 89, 139] .L)))))))))) (.W 1994623 [7] (.B 1994623 (.W 3989245 [3, 7] (.W 6152191 [3, 5, 7]
  (.B 6152191 (.W 12304381 [3, 47] (.W 16777183 [7, 19, 1531] (.B 16777183 (.W 33554365 [3, 7] .L) (.W
  33554365 [3, 7] .L)))) (.W 12304381 [3, 47, 541] (.W 16777183 [3, 7, 1531] (.B 16777183 (.W 33554365 [3, 7,
  89] .L) (.W 33554365 [3, 7, 89] .L))))))) (.W 3989245 [3, 7] (.W 6152191 [3, 5, 7] (.B 6152191 (.W 12304381
  [3, 5, 47] (.W 16777183 [3, 19, 1531] (.B 16777183 .L .L))) (.W 12304381 [3, 5, 47, 541] .L)))))))))))) (.W
  1048447 [3] (.B 1048447 (.W 1202743 [3] (.B 1202743 (.W 1994623 [7] (.B 1994623 (.W 2096893 [] (.B 2096893
  (.W 4193785 [3, 5, 7] (.W 6152191 [3, 5] (.B 6152191 (.W 9621943 [3, 47] (.B 9621943 (.W 19243885 [3, 7,
  19] (.W 38487769 [3, 5, 31] (.W 49217527 [3] (.B 49217527 (.W 98435053 [3, 5, 211] .L) (.W 98435053 [3, 5,
  211] .L))))) (.W 19243885 [3, 7, 19] (.W 38487769 [3, 31] (.W 49217527 [5] (.B 49217527 .L .L)))))) (.W
  9621943 [3, 47] (.B 9621943 (.W 19243885 [3, 7] (.W 38487769 [3, 5, 31, 89] .L)) (.W 19243885 [3, 7] (.W
  38487769 [3, 31, 89] .L))))))) (.W 4193785 [3, 5, 7] (.W 6152191 [3] (.B 6152191 (.W 9621943 [3, 5, 47] (.B
  9621943 (.W 19243885 [3, 7, 19] .L) (.W 19243885 [3, 7, 19] .L))) (.W 9621943 [3, 5, 47] (.B 9621943 (.W
  19243885 [3, 7] .L) (.W 19243885 [3, 7] .L)))))))) (.W 2096893 [] (.B 2096893 (.W 4193785 [3, 5, 7] (.W
  6152191 [3, 5] (.B 6152191 (.W 9621943 [3, 5, 47] (.B 9621943 (.W 19243885 [3, 7, 19] .L) (.W 19243885 [3,
  7, 19] .L))) (.W 9621943 [3, 5, 47] (.B 9621943 (.W 19243885 [3, 7] .L) (.W 19243885 [3, 7] .L)))))) (.W
  4193785 [3, 5, 7] (.W 6152191 [3] (.B 6152191 (.W 9621943 [5, 47] (.B 9621943 (.W 19243885 [3, 19] .L) .L))
  (.W 9621943 [5, 47] (.B 9621943 .L .L))))))))) (.W 1994623 [7] (.B 1994623 (.W 2096893 [] (.B 2096893 (.W
  4193785 [3, 5, 7] (.W 6152191 [3, 5] (.B 6152191 (.W 12304381 [3, 47] .L) (.W 12304381 [3, 47] .L)))) (.W
  4193785 [3, 5, 7] (.W 6152191 [3, 5] (.B 6152191 (.W 12304381 [3, 5, 47] .L) (.W 12304381 [3, 5, 47]
  .L)))))) (.W 2096893 [] (.B 2096893 (.W 4193785 [3, 7] (.W 6152191 [3, 5] (.B 6152191 (.W 12304381 [3, 5,
  47] .L) (.W 12304381 [3, 5, 47] .L)))) (.W 4193785 [3, 7] (.W 6152191 [3, 5] (.B 6152191 .L .L))))))))) (.W
  1202743 [3] (.B 1202743 (.W 1994623 [7] (.B 1994623 (.W 3989245 [3, 5, 7] (.W 6152191 [3, 5, 7] (.B 6152191
  (.W 9621943 [3, 47] (.B 9621943 .L .L)) (.W 9621943 [3, 47] (.B 9621943 .L .L))))) (.W 3989245 [3, 5, 7]
  (.W 6152191 [3, 7] (.B 6152191 .L .L))))) (.W 1994623 [7] (.B 1994623 (.W 3989245 [3, 7] (.W 6152191 [3, 5,
  7] (.B 6152191 .L .L))) (.W 3989245 [3, 7] .L)))))))))))) (.W 262111 [3] (.B 262111 (.W 524221 [3, 5, 29]
  (.W 524221 [] (.B 524221 (.W 524287 [] (.B 524287 (.W 1048573 [3, 5, 17] (.W 1048573 [] (.B 1048573 (.W
  1994623 [3, 7] (.B 1994623 (.W 3989245 [3, 5, 7, 97] (.W 6152191 [3, 5, 41] (.B 6152191 (.W 12304381 [3, 5,
  7, 47] (.W 24608761 [3, 7, 19, 1447] .L)) (.W 12304381 [3, 5, 7, 47] (.W 24608761 [3, 7, 1447] .L))))) (.W
  3989245 [3, 5, 7, 97] (.W 6152191 [3, 41] (.B 6152191 (.W 12304381 [3, 5, 7, 47] (.W 24608761 [3, 19, 1447]
  .L)) (.W 12304381 [3, 5, 7, 47] .L)))))) (.W 1994623 [3, 7] (.B 1994623 (.W 3989245 [3, 7, 97] (.W 6152191
  [3, 5, 41] (.B 6152191 (.W 12304381 [3, 5, 47] .L) (.W 12304381 [3, 5, 47] .L)))) (.W 3989245 [3, 7, 97]
  (.W 6152191 [3, 5, 41] (.B 6152191 (.W 12304381 [3, 5, 47] .L) (.W 12304381 [3, 5, 47] .L))))))))) (.W
  1048573 [3, 5, 17] (.W 1994623 [3, 7] (.B 1994623 (.W 3989245 [3, 7, 97] .L) (.W 3989245 [3, 7, 97]
  .L)))))) (.W 524287 [] (.B 524287 (.W 1048573 [3, 5] (.W 1048573 [] (.B 1048573 (.W 1994623 [3, 7] (.B
  1994623 (.W 3989245 [3, 5, 7, 13, 97] (.W 6152191 [3, 5] (.B 6152191 .L .L))) (.W 3989245 [3, 5, 7, 13, 97]
  (.W 6152191 [3] (.B 6152191 .L .L))))) (.W 1994623 [3, 7] (.B 1994623 (.W 3989245 [3, 7, 13, 97] .L) (.W
  3989245 [3, 7, 13, 97] .L)))))) (.W 1048573 [3, 5] (.W 1994623 [3, 7] (.B 1994623 (.W 3989245 [3, 7, 13,
  97] .L) .L)))))))) (.W 524221 [3, 5, 29] (.W 524287 [3] (.B 524287 (.W 1048447 [3, 5] (.B 1048447 (.W
  1048573 [] (.B 1048573 (.W 1994623 [3, 7] (.B 1994623 (.W 2096893 [] (.B 2096893 (.W 4193785 [3, 5, 7, 97]
  .L) (.W 4193785 [3, 5, 7, 97] .L))) (.W 2096893 [] (.B 2096893 (.W 4193785 [3, 5, 7, 97] .L) (.W 4193785
  [3, 5, 7, 97] .L))))) (.W 1994623 [3, 7] (.B 1994623 (.W 2096893 [] (.B 2096893 (.W 4193785 [3, 5, 7, 97]
  .L) (.W 4193785 [3, 5, 7, 97] .L))) (.W 2096893 [] (.B 2096893 (.W 4193785 [3, 7, 97] .L) .L)))))) (.W
  1048573 [] (.B 1048573 (.W 1994623 [3, 7] (.B 1994623 (.W 3989245 [3, 5, 7, 97] .L) (.W 3989245 [3, 5, 7,
  97] .L))) (.W 1994623 [3, 7] (.B 1994623 .L .L)))))) (.W 1048447 [3, 5] (.B 1048447 (.W 1994623 [3, 7] (.B
  1994623 .L .L)) (.W 1994623 [3, 7] (.B 1994623 .L .L))))))))))))))) (.W 37585 [3, 5, 7] (.W 75169 [3, 7]
  (.W 131071 [3, 5, 7, 97] (.B 131071 (.W 262111 [3] (.B 262111 (.W 524221 [3, 5, 11, 13, 29] .L) .L)) (.W
  262111 [3] (.B 262111 .L .L)))))))))) (.W 16381 [] (.B 16381 (.W 18793 [3] (.B 18793 (.W 37585 [3, 7, 181]
  (.W 75169 [3, 5] (.W 131071 [3, 7, 97] (.B 131071 (.W 150343 [] (.B 150343 .U (.W 300685 [3, 11, 23] (.W
  524287 [3, 19, 29] (.B 524287 (.W 1048573 [3, 5, 13, 43] (.W 1048573 [] (.B 1048573 (.W 2097145 [3, 7, 233]
  (.W 4194271 [3, 5, 7, 97] (.B 4194271 (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 7, 47] .L) (.W
  12304381 [3, 5, 7, 47, 647] .L))) (.W 6152191 [3] (.B 6152191 (.W 12304381 [3, 5, 7, 47] .L) (.W 12304381
  [3, 5, 7, 47, 647] .L)))))) (.W 2097145 [3, 7, 233] (.W 4194271 [3, 5, 7, 97] (.B 4194271 (.W 6152191 [3,
  5] (.B 6152191 .L .L)) (.W 6152191 [3, 5] (.B 6152191 .L .L)))))))) (.W 1048573 [3, 5, 13, 43] (.W 2097145
  [3, 7, 233] (.W 4194271 [3, 5, 7, 97] (.B 4194271 .L .L))))))))) (.W 150343 [] (.B 150343 (.W 300685 [3,
  23] (.W 524287 [3, 5, 19, 29] (.B 524287 (.W 1048573 [3, 5, 43] (.W 1048573 [] (.B 1048573 (.W 1202743 [3]
  (.B 1202743 (.W 2405485 [3, 5, 7, 233] (.W 4810969 [3, 5, 7] (.W 6152191 [3] (.B 6152191 .L .L)))) (.W
  2405485 [3, 5, 7, 233] (.W 4810969 [3, 5, 7] .L)))) (.W 1202743 [3] (.B 1202743 (.W 2405485 [3, 7, 233] (.W
  4810969 [3, 5, 7] .L)) (.W 2405485 [3, 7, 233] (.W 4810969 [3, 5, 7] .L))))))) (.W 1048573 [3, 5, 43] (.W
  1202743 [3] (.B 1202743 (.W 2405485 [3, 7, 233] .L) (.W 2405485 [3, 7, 233] .L))))))) (.W 300685 [3, 23]
  (.W 524287 [3, 19, 29] (.B 524287 (.W 1048573 [3, 5, 43] (.W 1048573 [] (.B 1048573 (.W 2097145 [3, 7, 233]
  .L) (.W 2097145 [3, 7, 233] .L)))) (.W 1048573 [3, 5, 43] .L)))))))))) (.W 37585 [3, 7, 181] (.W 75169 [3,
  5] (.W 131071 [3, 5, 7, 97] (.B 131071 (.W 262141 [3, 23] .L) (.W 262141 [3, 23] .L))))))) (.W 18793 [3]
  (.B 18793 (.W 37585 [3, 7] (.W 75169 [3, 5, 7] (.W 131071 [3, 97] (.B 131071 (.W 150343 [] (.B 150343 (.W
  262111 [3, 23] (.B 262111 .L .L)) (.W 262111 [3, 23] (.B 262111 .L .L)))) (.W 150343 [] (.B 150343 (.W
  262111 [3, 23] (.B 262111 .L .L)) (.W 262111 [3, 23] (.B 262111 .L .L)))))))) (.W 37585 [3, 7] (.W 75169
  [3, 5, 7] (.W 131071 [3, 5, 97] (.B 131071 .L .L)))))))))) (.W 15583 [3] (.B 15583 (.W 16381 [5] (.B 16381
  (.W 32761 [3, 5, 7, 19] (.W 37591 [7, 181] (.B 37591 (.W 75181 [3] (.W 75181 [] (.B 75181 (.W 131071 [7,
  97] (.B 131071 (.W 262141 [3, 53] .L) (.W 262141 [3, 53] .L))) (.W 131071 [7, 97] (.B 131071 (.W 262141 [3]
  .L) (.W 262141 [3] .L)))))) (.W 75181 [3, 7] (.W 131071 [3, 5, 7, 97] (.B 131071 (.W 190753 [3, 7] (.B
  190753 .L .L)) .L)))))) (.W 32761 [3, 5, 7, 19] (.W 37591 [3, 7] (.B 37591 (.W 75181 [3, 7] (.W 75181 []
  (.B 75181 (.W 131071 [3, 7, 97] (.B 131071 .L .L)) (.W 131071 [3, 7, 97] (.B 131071 .L .L))))) (.W 75181
  [3, 7] (.W 131071 [3, 5, 7, 97] (.B 131071 .L .L)))))))) (.W 16381 [5] (.B 16381 (.W 32761 [3, 7, 19] (.W
  36037 [7, 181] (.B 36037 (.W 72073 [3, 7] (.W 72073 [] (.B 72073 (.W 131071 [3, 7, 97] (.B 131071 .L .L))
  (.W 131071 [3, 7, 97] (.B 131071 .L .L))))) (.W 37591 [] (.B 37591 (.W 75181 [3, 5] (.W 75181 [] (.B 75181
  (.W 131071 [3, 7, 97] (.B 131071 .L .L)) (.W 131071 [3, 7, 97] (.B 131071 .L .L))))) (.W 75181 [3, 5, 7]
  (.W 131071 [3, 5, 7, 97] (.B 131071 .L .L)))))))) (.W 32761 [3, 7, 19] (.W 36037 [3, 7] (.B 36037 (.W 72073
  [3, 7] .L) (.W 37591 [] (.B 37591 (.W 75181 [3, 5, 7] .L) (.W 75181 [3, 5, 7] .L)))))))))))) (.W 9397 []
  (.B 9397 (.W 15583 [3] (.B 15583 (.W 18793 [3] (.B 18793 (.W 37585 [5, 7] (.W 75169 [3, 5] (.W 131071 [3,
  7, 97] (.B 131071 .L .L)))) (.W 37585 [5, 7] (.W 75169 [3] .L)))) (.W 18793 [3] (.B 18793 (.W 37585 [3, 7]
  (.W 75169 [3, 5] .L)) (.W 37585 [3, 7] (.W 75169 [3, 5] .L)))))) (.W 15583 [3] (.B 15583 (.W 31165 [3, 5,
  7, 19] (.W 37591 [3, 5, 7] (.B 37591 (.W 75181 [3] .L) (.W 75181 [3, 7] .L)))) (.W 31165 [3, 5, 7, 19] (.W
  36037 [3, 7] (.B 36037 .L .L)))))))))))))) (.W 1501 [3, 5, 7] (.W 3001 [3, 23] (.W 6001 [3, 5, 17, 31] (.W
  8191 [3, 5] (.B 8191 (.W 9397 [] (.B 9397 .L .L)) .L))))))) (.W 751 [3, 7] (.B 751 (.W 1501 [3, 5, 7] (.W
  1951 [19] (.B 1951 (.W 3901 [3, 23] (.W 6007 [3, 5, 17, 47] (.B 6007 (.W 8191 [3] (.B 8191 (.W 9397 [] (.B
  9397 .L .L)) .L)) (.W 8191 [3] (.B 8191 .L .L))))) (.W 3901 [3, 23] (.W 4513 [3, 17] (.B 4513 (.W 6007 []
  (.B 6007 .L .L)) (.W 6007 [5] (.B 6007 .L .L)))))))) (.W 1501 [3, 5, 7] (.W 1951 [3] (.B 1951 (.W 3901 [3,
  23, 31] .L) (.W 3901 [3, 23, 31] .L))))))))) (.W 253 [3, 11] (.W 487 [3, 5] (.B 487 (.W 751 [3, 7] (.B 751
  (.W 1501 [3, 7] .L) (.W 1501 [3, 7] .L))) (.W 751 [3, 7] (.B 751 (.W 1501 [3, 7] .L) (.W 1501 [3, 7]
  .L)))))))))) (.W 73 [3] (.B 73 (.W 127 [3] (.B 127 (.W 253 [5, 11, 13] (.W 505 [3, 11] (.W 751 [3, 7, 11]
  (.B 751 (.W 991 [] (.B 991 (.W 1981 [3, 5, 19] (.W 3961 [3, 5, 7, 23] .L)) (.W 1981 [3, 5, 19] (.W 3961 [3,
  5, 23] .L)))) (.W 991 [] (.B 991 (.W 1981 [3, 5] (.W 3961 [3, 5, 7, 23, 31] .L)) (.W 1981 [3, 5] .L)))))))
  (.W 253 [5, 11, 13] (.W 505 [3] (.W 751 [7, 11] (.B 751 (.W 991 [] (.B 991 .L .L)) .L)))))) (.W 127 [3] (.B
  127 (.W 253 [3, 11, 13] (.W 505 [3, 5, 11] (.W 751 [3, 7] (.B 751 .L .L)))) (.W 253 [3, 11, 13] (.W 505 [3,
  5] .L)))))))) (.W 61 [] (.B 61 (.W 73 [3] (.B 73 (.W 127 [5, 11] (.B 127 (.W 191 [5] (.B 191 (.W 381 [3,
  11] (.W 487 [3] (.B 487 (.W 973 [3, 7, 11] (.W 1945 [3, 5, 7] (.W 3889 [3, 5, 23] .L))) (.W 973 [3, 7, 11]
  (.W 1945 [3, 5] (.W 1951 [] (.B 1951 (.W 3901 [3, 5, 23] .L) (.W 3901 [3, 5, 23] .L)))))))) (.W 381 [3, 5,
  11] (.W 383 [] (.B 383 (.W 487 [] (.B 487 (.W 973 [3, 7, 11] (.W 1531 [3, 5, 7] (.B 1531 (.W 3061 [3, 5,
  23] .L) (.W 3061 [3, 5, 23] .L)))) (.W 973 [3, 7, 11] (.W 1531 [3, 5] (.B 1531 .L .L))))) (.W 487 [19] (.B
  487 (.W 761 [3, 7, 11] (.B 761 (.W 1521 [3, 7] .L) (.W 1521 [3, 5, 7, 13] .L))) (.W 761 [3, 7, 11, 17] (.B
  761 (.W 1521 [3] .L) (.W 1521 [3, 5, 7, 13] .L)))))))))) (.W 191 [5] (.B 191 (.W 381 [3] (.W 487 [3] (.B
  487 (.W 973 [7, 11] .L) (.W 973 [7, 11] .L)))) (.W 381 [3, 5] (.W 383 [] (.B 383 (.W 487 [] (.B 487 (.W 973
  [3, 7, 11] .L) (.W 973 [3, 7, 11] .L))) (.W 487 [19] (.B 487 (.W 973 [5, 7, 11, 13] .L) (.W 973 [5, 7, 11,
  13, 17] .L)))))))))) (.W 127 [5, 11] (.B 127 (.W 191 [3] (.B 191 (.W 381 [3, 5, 11] (.W 487 [3] (.B 487 (.W
  973 [3, 7] .L) (.W 973 [3, 7] .L)))) (.W 381 [3, 5, 11, 13] (.W 383 [] (.B 383 (.W 487 [] (.B 487 (.W 973
  [3, 7] .L) (.W 973 [3, 7] .L))) (.W 443 [] (.B 443 (.W 487 [] (.B 487 (.W 973 [3, 7] .L) .L)) (.W 487 []
  (.B 487 (.W 761 [3, 7] (.B 761 .L .L)) .L))))))))) (.W 191 [3] (.B 191 (.W 381 [3, 5] .L) (.W 381 [3, 5,
  13] .L))))))) (.W 73 [3] (.B 73 (.W 127 [3, 5] (.B 127 (.W 191 [5] (.B 191 (.W 381 [3, 11, 13] (.W 761 [3,
  7, 11] .L)) (.W 381 [3, 7, 11, 13] (.W 383 [] (.B 383 (.W 765 [3, 7, 11] .L) (.W 743 [3, 7, 11, 19] (.B 743
  .L .L))))))) (.W 191 [5] (.B 191 (.W 381 [3, 13] .L) (.W 381 [3, 7, 13] .L))))) (.W 127 [3, 5] (.B 127 (.W
  191 [3, 5] (.B 191 (.W 381 [3, 5, 11, 13] .L) (.W 381 [3, 5, 7, 11, 13] .L))) (.W 191 [3, 5] (.B 191 (.W
  381 [3, 5, 13] .L) (.W 381 [3, 5, 7, 13] .L))))))))))) (.W 47 [] (.B 47 (.W 61 [] (.B 61 (.W 121 [3] (.W
  127 [11] (.B 127 (.W 151 [] (.B 151 (.W 301 [3, 11] (.W 487 [3, 7] (.B 487 (.W 751 [3, 7] (.B 751 .L .L))
  (.W 751 [3, 7] (.B 751 .L .L))))) (.W 301 [3, 11] (.W 487 [3] (.B 487 .L .L))))) (.W 151 [] (.B 151 (.W 301
  [3, 11] (.W 487 [3, 7] (.B 487 .L .L))) (.W 301 [3, 11] .L)))))) (.W 121 [3] (.W 127 [3] (.B 127 (.W 151 []
  (.B 151 (.W 301 [3, 11, 13] .L) (.W 301 [3, 11, 13] .L))) (.W 151 [] (.B 151 (.W 301 [3, 11, 13] .L) (.W
  301 [3, 11, 13] .L)))))))) (.W 61 [] (.B 61 (.W 113 [3, 5] (.B 113 (.W 127 [11] (.B 127 (.W 253 [3] .L) (.W
  253 [3] .L))) (.W 127 [11] (.B 127 (.W 151 [] (.B 151 (.W 191 [] (.B 191 (.W 381 [3, 7, 11] .L) (.W 381 [3,
  5, 7, 11] .L))) (.W 191 [] (.B 191 (.W 381 [3, 11] .L) (.W 227 [] (.B 227 .L (.W 383 [3, 5, 11] (.B 383 .L
  .L)))))))) (.W 151 [] (.B 151 (.W 191 [] (.B 191 (.W 381 [3, 7] .L) .L)) (.W 191 [] (.B 191 .L .L))))))))
  (.W 113 [3, 5] (.B 113 (.W 127 [3] (.B 127 (.W 253 [3, 13] .L) .L)) (.W 127 [3] (.B 127 (.W 151 [] (.B 151
  (.W 191 [5] (.B 191 (.W 381 [3, 7, 11, 13] .L) (.W 381 [3, 7, 11, 13] .L))) (.W 191 [5] (.B 191 (.W 381 [3,
  11, 13] .L) .L)))) (.W 151 [] (.B 151 .L .L)))))))))))) (.W 37 [] (.B 37 (.W 47 [] (.B 47 (.W 73 [3] (.B 73
  (.W 127 [3] (.B 127 (.W 253 [5, 11] (.W 505 [3, 11] .L)) (.W 253 [5, 11] .L))) (.W 127 [3] (.B 127 (.W 253
  [3, 11] .L) (.W 253 [3, 11] .L))))) (.W 73 [3] (.B 73 (.W 127 [5] (.B 127 (.W 191 [5] (.B 191 .L .L)) .L))
  (.W 127 [5] (.B 127 (.W 191 [3] (.B 191 .L .L)) .L)))))) (.W 47 [] (.B 47 (.W 93 [3] (.W 127 [3] (.B 127
  (.W 151 [] (.B 151 .L .L)) .L))) (.W 93 [3] .L))))))))) (.W 23 [] (.B 23 (.W 31 [] (.B 31 (.W 61 [3] (.W 61
  [] (.B 61 (.W 79 [3] (.B 79 (.W 127 [7, 11] (.B 127 (.W 157 [] (.B 157 (.W 313 [3, 11] .L) (.W 313 [3, 11]
  .L))) (.W 157 [] (.B 157 (.W 313 [3] .L) (.W 313 [3] .L))))) (.W 127 [7, 11] (.B 127 (.W 229 [3] (.B 229 .L
  .L)) (.W 229 [3] (.B 229 .L .L)))))) (.W 79 [3] (.B 79 (.W 127 [3, 7] (.B 127 (.W 157 [] (.B 157 (.W 313
  [3, 11, 13] .L) (.W 313 [3, 11, 13] .L))) (.W 157 [] (.B 157 .L .L)))) (.W 127 [3, 7] (.B 127 (.W 229 [3]
  (.B 229 .L .L)) .L))))))) (.W 61 [3] (.W 79 [3] (.B 79 .L .L))))) (.W 29 [] (.B 29 (.W 31 [] (.B 31 (.W 61
  [3] (.W 61 [] (.B 61 (.W 121 [3, 5] .L) (.W 121 [3, 5] .L)))) (.W 61 [3] .L))) (.W 31 [] (.B 31 (.W 47 [3]
  (.B 47 (.W 61 [] (.B 61 (.W 79 [3] (.B 79 (.W 127 [3, 11] (.B 127 (.W 157 [] (.B 157 (.W 313 [3, 11] .L)
  (.W 313 [3, 11] .L))) (.W 157 [] (.B 157 .L .L)))) (.W 127 [3, 11] (.B 127 (.W 253 [3, 11] .L) .L)))) (.W
  79 [3] (.B 79 (.W 127 [3] (.B 127 (.W 157 [] (.B 157 .L .L)) .L)) (.W 127 [3] (.B 127 .L .L)))))) (.W 59 []
  (.B 59 (.W 61 [] (.B 61 (.W 121 [3] .L) (.W 121 [3] .L))) (.W 61 [] (.B 61 (.W 79 [3] (.B 79 (.W 127 [5,
  11] (.B 127 (.W 157 [] (.B 157 .L .L)) .L)) (.W 127 [5, 7, 11] (.B 127 .L .L)))) (.W 79 [3] (.B 79 (.W 127
  [3, 5] (.B 127 .L .L)) (.W 127 [3, 5, 7] (.B 127 .L .L)))))))))) (.W 47 [3] (.B 47 (.W 79 [3] (.B 79 .L
  .L)) (.W 59 [] (.B 59 .L .L)))))))))))))))) (.W 5 [] (.W 9 [] (.W 17 [3] .L)))))

-- Section 8. The step.

theorem step_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H2 := by
  refine ⟨63, fun n h hS he _ ha4 _ => ?_⟩
  by_contra hlt
  have hm : 64 ≤ padicValNat 2 n := by omega
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 5 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  have h5P : 5 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) :=
    fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self 5)
  generalize (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({5} : Finset ℕ)) = P at hP E h5P
  generalize padicValNat 2 n = m at E ha4 hm
  have hn5 : ∀ {c : ℕ}, c ≠ 5 → c ∉ ({5} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, -, S3, -, -, S6, S7, S8⟩ :=
    facts hP (prime_dvd_prime_pow (z := 5) (e := 2) (by norm_num)) E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one ha4
  have h13d : 13 ∣ 1 + 5 ^ 2 := by norm_num
  have h13P := S7 13 (by norm_num) (by norm_num) (hn5 (by norm_num)) h13d
  have h7P := S1 7 (by norm_num) (by norm_num) (hn5 (by norm_num)) 13 h13P (by norm_num)
  have hled : ¬ 5 ^ 2 ∣ ∏ p ∈ P, (p + 1) := fun hd => by
    have h1 : 5 * 5 ^ 2 ∣ (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) := by
      have e : (2 ^ m + 1) * (1 + 5 ^ 2) * ∏ p ∈ P, (p + 1) =
          (2 ^ m + 1) * (∏ p ∈ P, (p + 1)) * (1 + 5 ^ 2) := by ring
      rw [e]
      exact (Nat.mul_dvd_mul h5m hd).mul_right _
    rw [E] at h1
    have h2 : 5 ^ 2 * 5 ∣ 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
      have e : 5 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) = 2 ^ (m + 1) * 5 ^ 2 * ∏ p ∈ P, p := by ring
      rw [e, mul_comm (5 ^ 2) 5]
      exact h1
    have h3 : 5 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h3 with h4 | h4
    · have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow (by norm_num) h4)
      omega
    · obtain ⟨p, hp, hpd⟩ := (Prime.dvd_finsetProd_iff (Nat.Prime.prime (by norm_num)) _).mp h4
      have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) (hP p hp).1).mp hpd
      exact h5P (h5 ▸ hp)
  have e1 : (1 + 5 ^ 2 : ℕ) = 26 := by norm_num
  have e2 : (5 ^ 2 : ℕ) = 25 := by norm_num
  have C : Ctx P m :=
    { hP := hP
      E := by
        rw [e1, e2] at E
        exact E
      s1 := fun c hc hc2 hc5 p hp hd => S1 c hc hc2 (hn5 hc5) p hp hd
      s3 := fun c hc hc2 hc5 p hp p' hp' hd hd' => S3 c hc hc2 (hn5 hc5) p hp p' hp' hd hd'
      s6 := fun c hc hc2 hc5 p hp => S6 c hc hc2 (hn5 hc5) p hp
      hc13 := S8 13 (by norm_num) (by norm_num) (hn5 (by norm_num)) h13d
      led := hled
      hm := hm }
  refine sound C tree [7, 13] [5] 3 (by decide +kernel) ⟨fun x hx => ?_, by decide, fun y hy => ?_, fun p hp hp3 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl <;> assumption
  · rw [List.mem_singleton.mp hy]
    exact h5P
  · have hpp := (hP p hp).1
    have hp2 := (hP p hp).2
    interval_cases p <;> first | exact absurd rfl hp2 | exact absurd hpp (by norm_num)

end OMA.P_Erdos1052_z5_e2

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H1_R1.H2 :=
  OMA.P_Erdos1052_z5_e2.step_proof
