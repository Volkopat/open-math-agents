import OMAReductions.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1

/-!
# Step Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H2.R1.H1

Hypothesis H1 of reduction `Erdos1052.erdos_1052.R1.H2.R1.H1.R1.H2.R1.H4.R1.H2.R1` (unitary perfect numbers
`n = 2 ^ a * 11 ^ 2 * (simple odd primes)` with `a = 2 mod 4`, `7 ∣ n`, `¬ 13 ∣ n`): then `a ≤ 63`.

Credit: @aroth01. The base lemmas (`facts`, `path_bound`, `tail_bound`, `exists_child`, `kernel_balance_one`, ...)
are those of reductions `...R1.H2.R1.H1.R1` and `...R1.H2.R1.H1.R1.H2.R1`; @sanchan's reduction made this step.

Setting. `P` is the set of simple odd primes. `5 ∣ 2 ^ a + 1` and `61 ∣ 122` are simple primes that divide no
`p + 1`; `3` divides only `5 + 1` and `31` only `61 + 1`. Every other simple prime `p` has
`p + 1 = 2 ^ i * 11 ^ j * d` with `d` a product of distinct simple primes, each dividing only this `p + 1`.
Ledger: `11 ^ 3` does not divide the product of the `p + 1`. Balance: the product of the `1 + 1 / p` times
`(1 + 1 / 2 ^ a) * (122 / 121)` is `2`.

Proof. A search tree over statements `St P X Y N`: the members of the list `X` are simple primes, those of `Y`
are not, and every simple prime below `N` is in `X`.
* `extend` moves `N` to `N' < 2 * N`: a simple prime `p < N'` outside `X` has all the odd prime factors of `p + 1`
  below `N`, hence in `X` and open (dividing no `x + 1` with `x` in `X`), so `p` is one of finitely many
  numbers `2 ^ i * 11 ^ j * d - 1`; the computable check `winOk` finds a proper factor of each of them.
* `up_kill`: the weight of `X` alone is at least `2`.
* `low_kill`: the unknown simple primes are at least `N` and lie on disjoint paths (`path_bound`) that start at a
  parent of an open member of `X`, at a prime `q` with `11 ∣ q + 1` (the ledger bounds their number) or at a
  Mersenne prime (`tail_bound`); so their weight is at most
  `((N + 1) / (N - 1)) ^ (opens + ledger) * (N + 1) / (N - 3)`, which is too small.
The tree (Section 6) has 77 nodes; it was found by an exact search and each of its lines is a kernel computation.
-/

namespace OMA.P_Erdos1052_z11_e2

open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1 (facts path_bound tail_bound exists_child two_mul_le B_step B_anti
  B_nonneg one_add_le_B kernel_balance_one two_pow_of_no_odd_prime five_dvd_two_pow_add_one prime_dvd_prime_pow)
open OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1 (simple_of_unique_repeated)

-- Section 1. The checks, as computable functions on lists of numbers.

/-- The products of the sublists of a list. -/
def subProds : List ℕ → List ℕ
  | [] => [1]
  | c :: t => subProds t ++ (subProds t).map (fun d => c * d)

/-- The open members of `X`: not 5, not 61, and dividing no `x + 1` with `x` in `X`. -/
def opens (X : List ℕ) : List ℕ :=
  X.filter (fun c => c != 5 && c != 61 && X.all (fun x => (x + 1) % c != 0))

/-- The product of the `x + 1`. -/
def succProd (X : List ℕ) : ℕ := (X.map (fun x => x + 1)).prod

/-- A candidate `v` is harmless: outside the window, known, excluded, or with a proper factor in `F`. -/
def candOk (X Y F : List ℕ) (N N' v : ℕ) : Bool :=
  decide (v < N) || decide (N' ≤ v) || decide (v ∈ X) || decide (v ∈ Y) ||
    F.any (fun f => decide (1 < f) && decide (f < v) && v % f == 0)

/-- The window check: every number `2 ^ i * 11 ^ j * d - 1`, with `d` a product of distinct open members of `X` and
`11 ^ j` allowed by the ledger of 11, is harmless. -/
def winOk (X Y F : List ℕ) (N N' : ℕ) : Bool :=
  decide (N' < 2 * N) && decide (N' < 2 ^ 24) &&
    (subProds (opens X)).all (fun d => [0, 1, 2].all (fun j =>
      (11 ^ j * succProd X) % 11 ^ 3 == 0 ||
        (List.range 24).all (fun i => candOk X Y F N N' (2 ^ (i + 1) * (11 ^ j * d) - 1))))

/-- The weight of `X` alone is already too large. -/
def upOk (X : List ℕ) : Bool := decide (2 * 121 * X.prod ≤ 122 * succProd X)

/-- How many more simple primes `q` can have `11 ∣ q + 1`. -/
def ledgerLeft (X : List ℕ) : ℕ :=
  if (11 ^ 1 * succProd X) % 11 ^ 3 == 0 then 0 else if (11 ^ 2 * succProd X) % 11 ^ 3 == 0 then 1 else 2

/-- The weight of `X` together with everything that can still come above `N` is too small. -/
def lowOk (X : List ℕ) (N : ℕ) : Bool :=
  decide (5 ≤ N) &&
    decide ((2 ^ 64 + 1) * 122 * succProd X * (N + 1) ^ ((opens X).length + ledgerLeft X + 1) <
      2 * 2 ^ 64 * 121 * X.prod * (N - 1) ^ ((opens X).length + ledgerLeft X) * (N - 3))

-- Section 2. The setting and the state of the search.

/-- What is known about the set `P` of simple odd primes of `n = 2 ^ m * 11 ^ 2 * ∏ P`, `m = 2 mod 4`. -/
structure Ctx (P : Finset ℕ) (m : ℕ) : Prop where
  hP : ∀ p ∈ P, p.Prime ∧ p ≠ 2
  E : (2 ^ m + 1) * 122 * ∏ p ∈ P, (p + 1) = 2 ^ (m + 1) * 121 * ∏ p ∈ P, p
  s1 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 11 → ∀ p ∈ P, c ∣ p + 1 → c ∈ P
  s3 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 11 → ∀ p ∈ P, ∀ p' ∈ P, c ∣ p + 1 → c ∣ p' + 1 → p = p'
  s6 : ∀ c : ℕ, c.Prime → c ≠ 2 → c ≠ 11 → ∀ p ∈ P, ¬ c * c ∣ p + 1
  h5 : ∀ p ∈ P, ¬ 5 ∣ p + 1
  h61 : ∀ p ∈ P, ¬ 61 ∣ p + 1
  led : ¬ 11 ^ 3 ∣ ∏ p ∈ P, (p + 1)
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

theorem mem_opens {X : List ℕ} {c : ℕ} (hc : c ∈ X) (h5 : c ≠ 5) (h61 : c ≠ 61)
    (h : ∀ x ∈ X, ¬ c ∣ x + 1) : c ∈ opens X := by
  refine List.mem_filter.mpr ⟨hc, ?_⟩
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true]
  exact ⟨⟨h5, h61⟩, fun x hx hmod => h x hx (Nat.dvd_of_mod_eq_zero hmod)⟩

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

theorem pow_mul_dvd {a b s : ℕ} (hab : a ≤ b) (h : 11 ^ 3 ∣ 11 ^ a * s) : 11 ^ 3 ∣ 11 ^ b * s :=
  h.trans (Nat.mul_dvd_mul_right (pow_dvd_pow 11 hab) s)

-- Section 4. The window lemma: the closure of the known set moves from `N` to `N'`.

theorem extend {m : ℕ} {P : Finset ℕ} (C : Ctx P m) {X Y F : List ℕ} {N N' : ℕ}
    (h : St P X Y N) (hchk : winOk X Y F N N' = true) : St P X Y N' := by
  obtain ⟨hXP, hXn, hY, hcl⟩ := h
  refine ⟨hXP, hXn, hY, fun p hp hpN' => ?_⟩
  by_cases hpN : p < N
  · exact hcl p hp hpN
  by_contra hpX
  simp only [winOk, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hchk
  obtain ⟨⟨hN2, hN24⟩, hall⟩ := hchk
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
  obtain ⟨j, d, hd, hjd⟩ := Nat.exists_eq_pow_mul_and_not_dvd (n := u) hu0 11 (by norm_num)
  have hdvd : d ∣ p + 1 := ⟨2 ^ i * 11 ^ j, by rw [hiu, hjd]; ring⟩
  have hprime : ∀ c : ℕ, c.Prime → c ∣ d → c ≠ 2 ∧ c ≠ 11 := fun c _ hcd =>
    ⟨fun h2 => hu (by rw [hjd]; exact (h2 ▸ hcd).mul_left _), fun h11 => hd (h11 ▸ hcd)⟩
  have hopen : ∀ c : ℕ, c.Prime → c ∣ d → c ∈ opens X := fun c hc hcd => by
    obtain ⟨hc2, hc11⟩ := hprime c hc hcd
    have hcp : c ∣ p + 1 := hcd.trans hdvd
    have hcP : c ∈ P := C.s1 c hc hc2 hc11 p hp hcp
    have h2c := two_mul_le hc hc2 hpp hp2 hcp
    have hcX : c ∈ X := hcl c hcP (by omega)
    refine mem_opens hcX (fun h5 => C.h5 p hp (h5 ▸ hcp)) (fun h61 => C.h61 p hp (h61 ▸ hcp)) fun x hx hcx => ?_
    exact hpX ((C.s3 c hc hc2 hc11 p hp x (hXP x hx) hcp hcx) ▸ hx)
  have hdD : d ∣ (opens X).prod := dvd_of_primes
    (fun c hc hcc => by
      obtain ⟨hc2, hc11⟩ := hprime c hc ((Dvd.intro c rfl : c ∣ c * c).trans hcc)
      exact C.s6 c hc hc2 hc11 p hp (hcc.trans hdvd))
    (fun c hc hcd => List.dvd_prod (hopen c hc hcd))
  have hmem : d ∈ subProds (opens X) := mem_subProds _
    (fun c hc => (C.hP c (hXP c (List.mem_filter.mp hc).1)).1) d hdD
  have hjdvd : 11 ^ j ∣ p + 1 := ⟨2 ^ i * d, by rw [hiu, hjd]; ring⟩
  have hj3 : j < 3 := by
    by_contra hj
    exact C.led (((pow_dvd_pow 11 (by omega : 3 ≤ j)).trans hjdvd).trans
      (Finset.dvd_prod_of_mem (fun q => q + 1) hp))
  have hi1 : 1 ≤ i := by
    by_contra hi
    have hi0 : i = 0 := by omega
    rw [hi0, pow_zero, one_mul] at hiu
    exact hu ⟨(p + 1) / 2, by omega⟩
  have hi24 : i ≤ 24 := by
    by_contra hi
    have h1 : 2 ^ 25 ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ i ≤ p + 1 := by
      rw [hiu]
      exact Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero hu0)
    norm_num at h1 hN24
    omega
  have h1 := hall d hmem j (by interval_cases j <;> decide)
  rw [Bool.or_eq_true] at h1
  rcases h1 with h1 | h1
  · have h2 : 11 ^ 3 ∣ 11 ^ j * succProd X := Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1)
    have h3 : 11 ^ j * succProd X ∣ (p + 1) * succProd X := Nat.mul_dvd_mul_right hjdvd _
    have h4 := prod_mul_dvd hXP hXn (T := {p}) (Finset.singleton_subset_iff.mpr hp)
      (fun q hq => (Finset.mem_singleton.mp hq) ▸ hpX)
    rw [Finset.prod_singleton] at h4
    exact C.led (h2.trans (h3.trans h4))
  · rw [List.all_eq_true] at h1
    have h2 := h1 (i - 1) (List.mem_range.mpr (by omega))
    have hv : 2 ^ (i - 1 + 1) * (11 ^ j * d) - 1 = p := by
      rw [Nat.sub_add_cancel hi1, ← hjd, ← hiu]
      rfl
    rw [hv] at h2
    simp only [candOk, Bool.or_eq_true, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at h2
    rcases h2 with (((h2 | h2) | h2) | h2) | ⟨f, -, ⟨hf1, hfp⟩, hmod⟩
    · exact hpN h2
    · omega
    · exact hpX h2
    · exact hY p h2 hp
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
  have key : 2 ^ (m + 1) * 121 * ((∏ p ∈ P \ X.toFinset, p) * X.prod) <
      (2 ^ m + 1) * 122 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) :=
    calc 2 ^ (m + 1) * 121 * ((∏ p ∈ P \ X.toFinset, p) * X.prod)
        = 2 ^ m * ((∏ p ∈ P \ X.toFinset, p) * (2 * 121 * X.prod)) := by ring
      _ ≤ 2 ^ m * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (122 * succProd X)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul hQ hchk)
      _ < (2 ^ m + 1) * ((∏ p ∈ P \ X.toFinset, (p + 1)) * (122 * succProd X)) :=
          Nat.mul_lt_mul_of_pos_right (Nat.lt_succ_self _) (Nat.mul_pos hpos (Nat.mul_pos (by norm_num) hSpos))
      _ = (2 ^ m + 1) * 122 * ((∏ p ∈ P \ X.toFinset, (p + 1)) * succProd X) := by ring
  exact absurd E.symm (Nat.ne_of_lt key)

theorem balance_q {m : ℕ} {P : Finset ℕ} (C : Ctx P m) :
    (1 + 1 / (2 : ℚ) ^ m) * (122 / 121) * ∏ p ∈ P, (1 + 1 / (p : ℚ)) = 2 := by
  have hpos : ∀ p ∈ P, 0 < p := fun p hp => (C.hP p hp).1.pos
  have hY : (0 : ℚ) < ∏ p ∈ P, (p : ℚ) := Finset.prod_pos fun p hp => by exact_mod_cast hpos p hp
  have hcast : ((2 : ℚ) ^ m + 1) * 122 * ∏ p ∈ P, ((p : ℚ) + 1) = 2 ^ (m + 1) * 121 * ∏ p ∈ P, (p : ℚ) := by
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
    (h : (2 ^ 64 + 1) * 122 * S * (N + 1) ^ (E + 1) < 2 * 2 ^ 64 * 121 * Pi * (N - 1) ^ E * (N - 3)) :
    (1 + 1 / (2 : ℚ) ^ 64) * (122 / 121) * ((S : ℚ) / Pi) * (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ E *
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
  have e : (1 + 1 / (2 : ℚ) ^ 64) * (122 / 121) * ((S : ℚ) / Pi) * ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 1)) ^ E *
      ((((k + 3 : ℕ) : ℚ) + 1) / (((k + 3 : ℕ) : ℚ) - 3)) =
      (((2 : ℚ) ^ 64 + 1) * 122 * S * ((k : ℚ) + 3 + 1) ^ (E + 1)) /
        (2 ^ 64 * 121 * Pi * ((k : ℚ) + 2) ^ E * k) := by
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
  obtain ⟨g, hg⟩ := exists_child ({11} : Finset ℕ)
  have hn11 : ∀ {c : ℕ}, c ∉ ({11} : Finset ℕ) → c ≠ 11 := fun h h' => h (Finset.mem_singleton.mpr h')
  have hQP : ∀ q ∈ P.filter (fun p => p ∉ X), q ∈ P := fun q hq => (Finset.mem_filter.mp hq).1
  have hQX : ∀ q ∈ P.filter (fun p => p ∉ X), q ∉ X := fun q hq => (Finset.mem_filter.mp hq).2
  have hQN : ∀ q ∈ P.filter (fun p => p ∉ X), N ≤ q := fun q hq => by
    by_contra hlt
    exact hQX q hq (hcl q (hQP q hq) (by omega))
  have hgp : ∀ p ∈ P, g p ≠ 1 → (g p).Prime ∧ g p ≠ 2 ∧ g p ≠ 11 ∧ g p ∈ P ∧ 2 * g p ≤ p + 1 :=
    fun p hp h1 => by
      obtain ⟨hc, hc2, hcN⟩ := (hg p).2.2.1 h1
      exact ⟨hc, hc2, hn11 hcN, C.s1 _ hc hc2 (hn11 hcN) p hp (hg p).1,
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
      obtain ⟨hc, hc2, hc11, -, -⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact C.s3 _ hc hc2 hc11 q (hQP q hq) q' (hQP q' hq') (hg q).1 (he ▸ (hg q').1))
    (fun q hq => one_add_le_B (C.hP q (hQP q hq)).1.two_le)
    (fun q hq hgq => by
      obtain ⟨hc, -, -, -, h2⟩ := hgp q (hQP q hq) (hg1 q hq hgq)
      exact B_step hc.two_le h2)
  -- the roots of the forest of unknown primes
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
    obtain ⟨hc, hc2, hc11, hcP, -⟩ := hgp q hqP h1
    have hcX : g q ∈ X := by
      by_contra hcX
      exact hRg q hq (Finset.mem_filter.mpr ⟨hcP, hcX⟩)
    refine mem_opens hcX (fun h5 => C.h5 q hqP (h5 ▸ (hg q).1)) (fun h61 => C.h61 q hqP (h61 ▸ (hg q).1))
      fun x hx hcx => ?_
    exact hQX q (hRQ q hq) ((C.s3 _ hc hc2 hc11 q hqP x (hXP x hx) (hg q).1 hcx) ▸ hx)
  have hN2 : (2 : ℚ) ≤ N := by exact_mod_cast (by omega : 2 ≤ N)
  have hβN : ∀ q ∈ R, ((q : ℚ) + 1) / ((q : ℚ) - 1) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := fun q hq =>
    B_anti (by omega) (hQN q (hRQ q hq))
  have hβ0 : ∀ q ∈ R, (0 : ℚ) ≤ ((q : ℚ) + 1) / ((q : ℚ) - 1) := fun q hq =>
    B_nonneg (C.hP q (hRP q hq)).1.pos
  have hBN1 : (1 : ℚ) ≤ ((N : ℚ) + 1) / ((N : ℚ) - 1) := by
    rw [le_div_iff₀ (by linarith)]
    linarith
  -- class A: the least child is an open member of X
  have hcardA : (R.filter (fun q => g q ≠ 1)).card ≤ (opens X).length := by
    refine (Finset.card_le_card_of_injOn g (t := (opens X).toFinset) ?_ ?_).trans (List.toFinset_card_le _)
    · intro q hq
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      exact Finset.mem_coe.mpr (List.mem_toFinset.mpr (hA q hqR h1))
    · intro q hq q' hq' he
      obtain ⟨hqR, h1⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq)
      obtain ⟨hqR', -⟩ := Finset.mem_filter.mp (Finset.mem_coe.mp hq')
      obtain ⟨hc, hc2, hc11, -, -⟩ := hgp q (hRP q hqR) h1
      exact C.s3 _ hc hc2 hc11 q (hRP q hqR) q' (hRP q' hqR') (hg q).1 (he ▸ (hg q').1)
  -- class B: leaves with 11 | q + 1, counted by the ledger
  have hledB : ¬ 11 ^ 3 ∣ 11 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1)).card * succProd X :=
    fun hd => by
      have hsub : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1), q ∈ R := fun q hq =>
        (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1
      have h1 := prod_mul_dvd hXP hXn (T := (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1))
        (fun q hq => hRP q (hsub q hq)) (fun q hq => hQX q (hRQ q (hsub q hq)))
      have h2 : 11 ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1)).card ∣
          ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1), (q + 1) := by
        rw [← Finset.prod_const]
        exact Finset.prod_dvd_prod_of_dvd _ _ fun q hq => (Finset.mem_filter.mp hq).2
      exact C.led (hd.trans ((Nat.mul_dvd_mul_right h2 _).trans h1))
  have hcardB : ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1)).card ≤ ledgerLeft X := by
    unfold ledgerLeft
    by_contra hlt
    apply hledB
    split_ifs at hlt with h1 h2
    · exact pow_mul_dvd (by omega) (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h1))
    · exact pow_mul_dvd (by omega) (Nat.dvd_of_mod_eq_zero (beq_iff_eq.mp h2))
    · exact pow_mul_dvd (by omega : 3 ≤ _) (Dvd.intro _ rfl)
  -- class C: Mersenne leaves
  have hpow : ∀ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 11 ∣ q + 1), ∃ k, q + 1 = 2 ^ k :=
    fun q hq => by
      obtain ⟨hq1, h11⟩ := Finset.mem_filter.mp hq
      obtain ⟨-, hg1'⟩ := Finset.mem_filter.mp hq1
      refine two_pow_of_no_odd_prime fun c hc hc2 hcd => ?_
      have := (hg q).2.1 (not_not.mp hg1') c hc hc2 hcd
      rw [Finset.mem_singleton] at this
      exact h11 (this ▸ hcd)
  have hprodC : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => ¬ 11 ∣ q + 1),
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
  have hprodB : ∏ q ∈ (R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1),
      (((q : ℚ) + 1) / ((q : ℚ) - 1)) ≤
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1)).card := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod (fun q hq => hβ0 q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
      (fun q hq => hβN q (Finset.mem_filter.mp (Finset.mem_filter.mp hq).1).1)
  have hsplit1 := Finset.prod_filter_mul_prod_filter_not R (fun q => g q ≠ 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hsplit2 := Finset.prod_filter_mul_prod_filter_not (R.filter (fun q => ¬ g q ≠ 1)) (fun q => 11 ∣ q + 1)
    (fun q => ((q : ℚ) + 1) / ((q : ℚ) - 1))
  have hpowle : (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ (R.filter (fun q => g q ≠ 1)).card *
      (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((R.filter (fun q => ¬ g q ≠ 1)).filter (fun q => 11 ∣ q + 1)).card ≤
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
  -- the known part
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
  have hchain : (1 + 1 / (2 : ℚ) ^ m) * (122 / 121) *
      ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ))) ≤
      (1 + 1 / (2 : ℚ) ^ 64) * (122 / 121) * ((succProd X : ℚ) / (X.prod : ℚ)) *
        (((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) * (((N : ℚ) + 1) / ((N : ℚ) - 3)) := by
    have h1 : (1 + 1 / (2 : ℚ) ^ m) * (122 / 121) ≤ (1 + 1 / (2 : ℚ) ^ 64) * (122 / 121) :=
      mul_le_mul_of_nonneg_right (by linarith) (by norm_num)
    have h2 : (succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)) ≤
        (succProd X : ℚ) / (X.prod : ℚ) * ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
          (((N : ℚ) + 1) / ((N : ℚ) - 3))) := mul_le_mul_of_nonneg_left hQle hSq
    calc (1 + 1 / (2 : ℚ) ^ m) * (122 / 121) *
        ((succProd X : ℚ) / (X.prod : ℚ) * ∏ p ∈ P.filter (fun p => p ∉ X), (1 + 1 / (p : ℚ)))
        ≤ (1 + 1 / (2 : ℚ) ^ 64) * (122 / 121) * ((succProd X : ℚ) / (X.prod : ℚ) *
          ((((N : ℚ) + 1) / ((N : ℚ) - 1)) ^ ((opens X).length + ledgerLeft X) *
            (((N : ℚ) + 1) / ((N : ℚ) - 3)))) :=
          mul_le_mul h1 h2 (mul_nonneg hSq hQ0) (by positivity)
      _ = _ := by ring
  linarith

-- Section 6. The search tree (written by a script from an exact search; every line is checked by the kernel).

theorem tree {m : ℕ} {P : Finset ℕ} (C : Ctx P m) (h0 : St P [3, 5, 7, 31, 61] [13] 8) : False := by
  have h1 := extend C h0 (F := []) (N' := 15) (by decide +kernel)
  have h2 := extend C h1 (F := [3]) (N' := 29) (by decide +kernel)
  have h3 := extend C h2 (F := []) (N' := 43) (by decide +kernel)
  by_cases q43 : 43 ∈ P
  · have h4 := incl h3 q43 (by decide)
    have h5 := extend C h4 (F := [3, 5]) (N' := 85) (by decide +kernel)
    have h6 := extend C h5 (F := [3, 5]) (N' := 127) (by decide +kernel)
    by_cases q127 : 127 ∈ P
    · have h7 := incl h6 q127 (by decide)
      have h8 := extend C h7 (F := [3, 5]) (N' := 223) (by decide +kernel)
      by_cases q223 : 223 ∈ P
      · have h9 := incl h8 q223 (by decide)
        exact up_kill C h9 (by decide +kernel)
      · have h10 := excl h8 q223
        have h11 := extend C h10 (F := [3, 11]) (N' := 307) (by decide +kernel)
        by_cases q307 : 307 ∈ P
        · have h12 := incl h11 q307 (by decide)
          exact up_kill C h12 (by decide +kernel)
        · have h13 := excl h11 q307
          have h14 := extend C h13 (F := [3, 7]) (N' := 601) (by decide +kernel)
          by_cases q601 : 601 ∈ P
          · have h15 := incl h14 q601 (by decide)
            have h16 := extend C h15 (F := [3, 5, 19]) (N' := 1201) (by decide +kernel)
            have h17 := extend C h16 (F := []) (N' := 1201) (by decide +kernel)
            by_cases q1201 : 1201 ∈ P
            · have h18 := incl h17 q1201 (by decide)
              have h19 := extend C h18 (F := [3, 23]) (N' := 2401) (by decide +kernel)
              have h20 := extend C h19 (F := [3, 5, 7, 17]) (N' := 4801) (by decide +kernel)
              have h21 := extend C h20 (F := [3, 37]) (N' := 8191) (by decide +kernel)
              by_cases q8191 : 8191 ∈ P
              · have h22 := incl h21 q8191 (by decide)
                exact up_kill C h22 (by decide +kernel)
              · have h23 := excl h21 q8191
                have h24 := extend C h23 (F := [3, 5, 7, 13]) (N' := 16381) (by decide +kernel)
                have h25 := extend C h24 (F := [3, 7]) (N' := 32761) (by decide +kernel)
                have h26 := extend C h25 (F := [7]) (N' := 38431) (by decide +kernel)
                by_cases q38431 : 38431 ∈ P
                · have h27 := incl h26 q38431 (by decide)
                  have h28 := extend C h27 (F := [3, 5, 7]) (N' := 76861) (by decide +kernel)
                  have h29 := extend C h28 (F := [3, 29, 101]) (N' := 131071) (by decide +kernel)
                  by_cases q131071 : 131071 ∈ P
                  · have h30 := incl h29 q131071 (by decide)
                    have h31 := extend C h30 (F := [3, 5, 229]) (N' := 262141) (by decide +kernel)
                    have h32 := extend C h31 (F := [3, 7, 11, 43]) (N' := 524281) (by decide +kernel)
                    have h33 := extend C h32 (F := [3]) (N' := 524287) (by decide +kernel)
                    by_cases q524287 : 524287 ∈ P
                    · have h34 := incl h33 q524287 (by decide)
                      have h35 := extend C h34 (F := [3, 5, 13, 17]) (N' := 1048573) (by decide +kernel)
                      have h36 := extend C h35 (F := []) (N' := 1048573) (by decide +kernel)
                      by_cases q1048573 : 1048573 ∈ P
                      · have h37 := incl h36 q1048573 (by decide)
                        have h38 := extend C h37 (F := [3, 7, 41, 71]) (N' := 2097145) (by decide +kernel)
                        exact low_kill C h38 (by decide +kernel)
                      · have h39 := excl h36 q1048573
                        have h40 := extend C h39 (F := [3, 7, 41, 71]) (N' := 2097145) (by decide +kernel)
                        exact low_kill C h40 (by decide +kernel)
                    · have h41 := excl h33 q524287
                      have h42 := extend C h41 (F := [3, 5, 13, 17]) (N' := 1048573) (by decide +kernel)
                      have h43 := extend C h42 (F := [3, 7, 41, 71]) (N' := 2097145) (by decide +kernel)
                      exact low_kill C h43 (by decide +kernel)
                  · have h44 := excl h29 q131071
                    have h45 := extend C h44 (F := [3, 5, 229]) (N' := 262141) (by decide +kernel)
                    have h46 := extend C h45 (F := [3, 7, 43]) (N' := 524281) (by decide +kernel)
                    have h47 := extend C h46 (F := []) (N' := 524287) (by decide +kernel)
                    by_cases q524287 : 524287 ∈ P
                    · have h48 := incl h47 q524287 (by decide)
                      have h49 := extend C h48 (F := [3, 5, 17]) (N' := 1048573) (by decide +kernel)
                      exact low_kill C h49 (by decide +kernel)
                    · have h50 := excl h47 q524287
                      have h51 := extend C h50 (F := [3, 5, 17]) (N' := 1048573) (by decide +kernel)
                      exact low_kill C h51 (by decide +kernel)
                · have h52 := excl h26 q38431
                  have h53 := extend C h52 (F := [3, 5, 7]) (N' := 76861) (by decide +kernel)
                  have h54 := extend C h53 (F := [3, 29]) (N' := 131071) (by decide +kernel)
                  by_cases q131071 : 131071 ∈ P
                  · have h55 := incl h54 q131071 (by decide)
                    have h56 := extend C h55 (F := [3, 5, 7, 229]) (N' := 262141) (by decide +kernel)
                    have h57 := extend C h56 (F := [3, 7, 11, 43]) (N' := 524281) (by decide +kernel)
                    exact low_kill C h57 (by decide +kernel)
                  · have h58 := excl h54 q131071
                    have h59 := extend C h58 (F := [3, 5, 7, 229]) (N' := 262141) (by decide +kernel)
                    exact low_kill C h59 (by decide +kernel)
            · have h60 := excl h17 q1201
              have h61 := extend C h60 (F := [3, 23]) (N' := 2401) (by decide +kernel)
              have h62 := extend C h61 (F := [3, 5, 17]) (N' := 4801) (by decide +kernel)
              have h63 := extend C h62 (F := [3, 11, 37]) (N' := 8191) (by decide +kernel)
              by_cases q8191 : 8191 ∈ P
              · have h64 := incl h63 q8191 (by decide)
                have h65 := extend C h64 (F := [3, 5, 7]) (N' := 16381) (by decide +kernel)
                exact low_kill C h65 (by decide +kernel)
              · have h66 := excl h63 q8191
                have h67 := extend C h66 (F := [3, 5, 7]) (N' := 16381) (by decide +kernel)
                exact low_kill C h67 (by decide +kernel)
          · have h68 := excl h14 q601
            have h69 := extend C h68 (F := [3, 5, 19]) (N' := 1201) (by decide +kernel)
            have h70 := extend C h69 (F := [3]) (N' := 1231) (by decide +kernel)
            by_cases q1231 : 1231 ∈ P
            · have h71 := incl h70 q1231 (by decide)
              have h72 := extend C h71 (F := [3, 5, 23]) (N' := 2461) (by decide +kernel)
              have h73 := extend C h72 (F := [3, 17, 23]) (N' := 4921) (by decide +kernel)
              have h74 := extend C h73 (F := [3]) (N' := 5503) (by decide +kernel)
              by_cases q5503 : 5503 ∈ P
              · have h75 := incl h74 q5503 (by decide)
                have h76 := extend C h75 (F := [3]) (N' := 8191) (by decide +kernel)
                by_cases q8191 : 8191 ∈ P
                · have h77 := incl h76 q8191 (by decide)
                  have h78 := extend C h77 (F := [5, 43]) (N' := 16381) (by decide +kernel)
                  exact low_kill C h78 (by decide +kernel)
                · have h79 := excl h76 q8191
                  exact low_kill C h79 (by decide +kernel)
              · have h80 := excl h74 q5503
                have h81 := extend C h80 (F := [3]) (N' := 8191) (by decide +kernel)
                by_cases q8191 : 8191 ∈ P
                · have h82 := incl h81 q8191 (by decide)
                  exact low_kill C h82 (by decide +kernel)
                · have h83 := excl h81 q8191
                  exact low_kill C h83 (by decide +kernel)
            · have h84 := excl h70 q1231
              have h85 := extend C h84 (F := [3, 5]) (N' := 1777) (by decide +kernel)
              by_cases q1777 : 1777 ∈ P
              · have h86 := incl h85 q1777 (by decide)
                have h87 := extend C h86 (F := [3, 5, 23, 31]) (N' := 3553) (by decide +kernel)
                have h88 := extend C h87 (F := [3, 11]) (N' := 5503) (by decide +kernel)
                by_cases q5503 : 5503 ∈ P
                · have h89 := incl h88 q5503 (by decide)
                  have h90 := extend C h89 (F := [3]) (N' := 8191) (by decide +kernel)
                  by_cases q8191 : 8191 ∈ P
                  · have h91 := incl h90 q8191 (by decide)
                    exact low_kill C h91 (by decide +kernel)
                  · have h92 := excl h90 q8191
                    exact low_kill C h92 (by decide +kernel)
                · have h93 := excl h88 q5503
                  exact low_kill C h93 (by decide +kernel)
              · have h94 := excl h85 q1777
                have h95 := extend C h94 (F := [3, 5, 23, 29, 31]) (N' := 3553) (by decide +kernel)
                have h96 := extend C h95 (F := [3]) (N' := 3583) (by decide +kernel)
                by_cases q3583 : 3583 ∈ P
                · have h97 := incl h96 q3583 (by decide)
                  have h98 := extend C h97 (F := [3, 17]) (N' := 5503) (by decide +kernel)
                  by_cases q5503 : 5503 ∈ P
                  · have h99 := incl h98 q5503 (by decide)
                    have h100 := extend C h99 (F := [3, 5, 37]) (N' := 8191) (by decide +kernel)
                    by_cases q8191 : 8191 ∈ P
                    · have h101 := incl h100 q8191 (by decide)
                      exact low_kill C h101 (by decide +kernel)
                    · have h102 := excl h100 q8191
                      exact low_kill C h102 (by decide +kernel)
                  · have h103 := excl h98 q5503
                    exact low_kill C h103 (by decide +kernel)
                · have h104 := excl h96 q3583
                  have h105 := extend C h104 (F := [3, 13, 17]) (N' := 5503) (by decide +kernel)
                  by_cases q5503 : 5503 ∈ P
                  · have h106 := incl h105 q5503 (by decide)
                    exact low_kill C h106 (by decide +kernel)
                  · have h107 := excl h105 q5503
                    exact low_kill C h107 (by decide +kernel)
    · have h108 := excl h6 q127
      have h109 := extend C h108 (F := [3, 5]) (N' := 223) (by decide +kernel)
      by_cases q223 : 223 ∈ P
      · have h110 := incl h109 q223 (by decide)
        have h111 := extend C h110 (F := [3, 7]) (N' := 445) (by decide +kernel)
        have h112 := extend C h111 (F := [3, 5, 7, 19]) (N' := 889) (by decide +kernel)
        have h113 := extend C h112 (F := [3, 5]) (N' := 1777) (by decide +kernel)
        exact low_kill C h113 (by decide +kernel)
      · have h114 := excl h109 q223
        have h115 := extend C h114 (F := [3]) (N' := 307) (by decide +kernel)
        by_cases q307 : 307 ∈ P
        · have h116 := incl h115 q307 (by decide)
          have h117 := extend C h116 (F := [7]) (N' := 613) (by decide +kernel)
          have h118 := extend C h117 (F := []) (N' := 613) (by decide +kernel)
          by_cases q613 : 613 ∈ P
          · have h119 := incl h118 q613 (by decide)
            have h120 := extend C h119 (F := [3]) (N' := 1225) (by decide +kernel)
            have h121 := extend C h120 (F := [5, 23]) (N' := 2449) (by decide +kernel)
            exact low_kill C h121 (by decide +kernel)
          · have h122 := excl h118 q613
            have h123 := extend C h122 (F := [3]) (N' := 1225) (by decide +kernel)
            exact low_kill C h123 (by decide +kernel)
        · have h124 := excl h115 q307
          have h125 := extend C h124 (F := [3, 7]) (N' := 601) (by decide +kernel)
          by_cases q601 : 601 ∈ P
          · have h126 := incl h125 q601 (by decide)
            have h127 := extend C h126 (F := [3, 19]) (N' := 1201) (by decide +kernel)
            exact low_kill C h127 (by decide +kernel)
          · have h128 := excl h125 q601
            have h129 := extend C h128 (F := [3, 5, 19]) (N' := 1201) (by decide +kernel)
            exact low_kill C h129 (by decide +kernel)
  · have h130 := excl h3 q43
    have h131 := extend C h130 (F := [3, 5]) (N' := 85) (by decide +kernel)
    have h132 := extend C h131 (F := [3]) (N' := 127) (by decide +kernel)
    by_cases q127 : 127 ∈ P
    · have h133 := incl h132 q127 (by decide)
      have h134 := extend C h133 (F := [3, 5]) (N' := 223) (by decide +kernel)
      by_cases q223 : 223 ∈ P
      · have h135 := incl h134 q223 (by decide)
        have h136 := extend C h135 (F := []) (N' := 241) (by decide +kernel)
        by_cases q241 : 241 ∈ P
        · have h137 := incl h136 q241 (by decide)
          have h138 := extend C h137 (F := [3, 5, 11]) (N' := 481) (by decide +kernel)
          have h139 := extend C h138 (F := [3, 7, 13]) (N' := 961) (by decide +kernel)
          exact low_kill C h139 (by decide +kernel)
        · have h140 := excl h136 q241
          have h141 := extend C h140 (F := [3, 5, 11]) (N' := 481) (by decide +kernel)
          have h142 := extend C h141 (F := [3, 7, 19]) (N' := 961) (by decide +kernel)
          exact low_kill C h142 (by decide +kernel)
      · have h143 := excl h134 q223
        have h144 := extend C h143 (F := []) (N' := 241) (by decide +kernel)
        by_cases q241 : 241 ∈ P
        · have h145 := incl h144 q241 (by decide)
          have h146 := extend C h145 (F := [3, 11]) (N' := 481) (by decide +kernel)
          exact low_kill C h146 (by decide +kernel)
        · have h147 := excl h144 q241
          have h148 := extend C h147 (F := [3, 11]) (N' := 307) (by decide +kernel)
          by_cases q307 : 307 ∈ P
          · have h149 := incl h148 q307 (by decide)
            have h150 := extend C h149 (F := [3, 7]) (N' := 613) (by decide +kernel)
            exact low_kill C h150 (by decide +kernel)
          · have h151 := excl h148 q307
            have h152 := extend C h151 (F := [3, 7]) (N' := 613) (by decide +kernel)
            exact low_kill C h152 (by decide +kernel)
    · have h153 := excl h132 q127
      have h154 := extend C h153 (F := [3, 5]) (N' := 223) (by decide +kernel)
      by_cases q223 : 223 ∈ P
      · have h155 := incl h154 q223 (by decide)
        have h156 := extend C h155 (F := []) (N' := 241) (by decide +kernel)
        by_cases q241 : 241 ∈ P
        · have h157 := incl h156 q241 (by decide)
          have h158 := extend C h157 (F := [3, 5]) (N' := 481) (by decide +kernel)
          exact low_kill C h158 (by decide +kernel)
        · have h159 := excl h156 q241
          have h160 := extend C h159 (F := [3, 5]) (N' := 481) (by decide +kernel)
          exact low_kill C h160 (by decide +kernel)
      · have h161 := excl h154 q223
        have h162 := extend C h161 (F := []) (N' := 241) (by decide +kernel)
        by_cases q241 : 241 ∈ P
        · have h163 := incl h162 q241 (by decide)
          have h164 := extend C h163 (F := [3]) (N' := 481) (by decide +kernel)
          exact low_kill C h164 (by decide +kernel)
        · have h165 := excl h162 q241
          have h166 := extend C h165 (F := [3]) (N' := 307) (by decide +kernel)
          by_cases q307 : 307 ∈ P
          · have h167 := incl h166 q307 (by decide)
            exact low_kill C h167 (by decide +kernel)
          · have h168 := excl h166 q307
            exact low_kill C h168 (by decide +kernel)

-- Section 7. The step.

theorem step_proof : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1.H1 := by
  refine ⟨63, fun n h hS he ha4 _ _ h7 h13 => ?_⟩
  by_contra hlt
  have hm : 64 ≤ padicValNat 2 n := by omega
  obtain ⟨hzn, hs⟩ := simple_of_unique_repeated h.2.ne' hS
  have hzpf : 11 ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨by norm_num, hzn, h.2.ne'⟩
  obtain ⟨hP, E⟩ := kernel_balance_one h hzpf (by norm_num) hs
  rw [Nat.factorization_def n Nat.prime_two, he] at E
  have h11P : 11 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({11} : Finset ℕ)) :=
    fun h => (Finset.mem_filter.mp h).2 (Finset.mem_singleton_self 11)
  have h7P : 7 ∈ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({11} : Finset ℕ)) :=
    Finset.mem_filter.mpr ⟨Finset.mem_erase.mpr ⟨by norm_num,
      Nat.mem_primeFactors.mpr ⟨by norm_num, h7, h.2.ne'⟩⟩, by decide⟩
  have h13P : 13 ∉ (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({11} : Finset ℕ)) :=
    fun h => h13 (Nat.dvd_of_mem_primeFactors (Finset.mem_of_mem_erase (Finset.mem_filter.mp h).1))
  generalize (n.primeFactors.erase 2).filter (fun r => ¬ r ∈ ({11} : Finset ℕ)) = P at hP E h11P h7P h13P
  generalize padicValNat 2 n = m at E ha4 hm
  have hn11 : ∀ {c : ℕ}, c ≠ 11 → c ∉ ({11} : Finset ℕ) := fun h h' => h (Finset.mem_singleton.mp h')
  obtain ⟨S1, S2, S3, S4, -, S6, S7, S8⟩ :=
    facts hP (prime_dvd_prime_pow (z := 11) (e := 2) (by norm_num)) E
  have h5m : 5 ∣ 2 ^ m + 1 := five_dvd_two_pow_add_one ha4
  have h61d : 61 ∣ 1 + 11 ^ 2 := by norm_num
  have h5P := S2 5 (by norm_num) (by norm_num) (hn11 (by norm_num)) h5m
  have h3P := S1 3 (by norm_num) (by norm_num) (hn11 (by norm_num)) 5 h5P (by norm_num)
  have h61P := S7 61 (by norm_num) (by norm_num) (hn11 (by norm_num)) h61d
  have h31P := S1 31 (by norm_num) (by norm_num) (hn11 (by norm_num)) 61 h61P (by norm_num)
  have hled : ¬ 11 ^ 3 ∣ ∏ p ∈ P, (p + 1) := fun hd => by
    have h1 : 11 ^ 3 ∣ 2 ^ (m + 1) * 11 ^ 2 * ∏ p ∈ P, p := E ▸ (hd.mul_left _)
    have h2 : 11 ^ 2 * 11 ∣ 11 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) := by
      have e : 11 ^ 2 * (2 ^ (m + 1) * ∏ p ∈ P, p) = 2 ^ (m + 1) * 11 ^ 2 * ∏ p ∈ P, p := by ring
      rw [e]
      exact h1
    have h3 : 11 ∣ 2 ^ (m + 1) * ∏ p ∈ P, p := Nat.dvd_of_mul_dvd_mul_left (by norm_num) h2
    rcases (Nat.Prime.dvd_mul (by norm_num)).mp h3 with h4 | h4
    · have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow (by norm_num) h4)
      omega
    · obtain ⟨p, hp, hpd⟩ := (Prime.dvd_finsetProd_iff (Nat.Prime.prime (by norm_num)) _).mp h4
      have h5 := (Nat.prime_dvd_prime_iff_eq (by norm_num) (hP p hp).1).mp hpd
      exact h11P (h5 ▸ hp)
  have e1 : (1 + 11 ^ 2 : ℕ) = 122 := by norm_num
  have e2 : (11 ^ 2 : ℕ) = 121 := by norm_num
  have C : Ctx P m :=
    { hP := hP
      E := by
        rw [e1, e2] at E
        exact E
      s1 := fun c hc hc2 hc11 p hp hd => S1 c hc hc2 (hn11 hc11) p hp hd
      s3 := fun c hc hc2 hc11 p hp p' hp' hd hd' => S3 c hc hc2 (hn11 hc11) p hp p' hp' hd hd'
      s6 := fun c hc hc2 hc11 p hp => S6 c hc hc2 (hn11 hc11) p hp
      h5 := S4 5 (by norm_num) (by norm_num) (hn11 (by norm_num)) h5m
      h61 := S8 61 (by norm_num) (by norm_num) (hn11 (by norm_num)) h61d
      led := hled
      hm := hm }
  refine tree C ⟨fun x hx => ?_, by decide, fun y hy => ?_, fun p hp hp8 => ?_⟩
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> assumption
  · rw [List.mem_singleton.mp hy]
    exact h13P
  · have hpp := (hP p hp).1
    have hp2 := (hP p hp).2
    interval_cases p <;> first | decide | exact absurd rfl hp2 | exact absurd hpp (by norm_num)

end OMA.P_Erdos1052_z11_e2

theorem OMA.solution : OMA.R_Erdos1052_erdos_1052_R1_H2_R1_H1_R1_H2_R1_H4_R1_H2_R1.H1 :=
  OMA.P_Erdos1052_z11_e2.step_proof
