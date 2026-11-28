import OMAReductions.R_OeisA215926_conjecture_1_R1_H1_R1
import Mathlib

-- Step OeisA215926.conjecture_1.R1.H1.R1.H1
-- Credit: @chinwas

/-!
# Odd almost perfect numbers have at least five distinct prime factors

Step `H1` of the reduction `OeisA215926.conjecture_1.R1.H1.R1`: no odd square `k` with exactly four
distinct prime factors satisfies `σ(k) = 2k - 1`.

Write `k = p₀^(2a) p₁^(2b) p₂^(2c) p₃^(2d)` with `p₀ < p₁ < p₂ < p₃` odd primes, `S = σ(p^(2e))`,
`X = p^(2e)`, so that `(p - 1) S + 1 = p X`.

1. **Abundancy** (`hi_bound`, `hi_cases`). `∏ (pᵢ - 1) · σ(k) < ∏ pᵢ · k` forces
   `2 ∏ (pᵢ - 1) ≤ ∏ pᵢ`, which leaves `p₀ = 3` and
   `(p₁, p₂) ∈ {(5,7), (5,11), (5,13)}` with `p₃` free, or a bounded `p₃`:
   `(5,17): p₃ ≤ 256`, `(5,19): p₃ ≤ 96`, `(5,23): p₃ ≤ 50`, `(5,29): p₃ ≤ 34`,
   `(7,11): p₃ ≤ 26`, `(7,13): p₃ ≤ 19`.
2. **Lower bounds** (`lo2`, `lo4`, `lo_contra`). `p² S ≥ (p² + p + 1) X` makes `3, 5, 7` too
   abundant; for `3, 5, 11` and `3, 5, 13` the same bound forces the exponent of `3` to be `2`.
3. **The largest prime** (`d_arg`, `bound11`, `bound13`). With `m = k / p₃^(2d)`,
   `p₃ (2m - σ(m)) < 2m`; this gives `p₃ < 144` for `3, 5, 11` and `p₃ < 46` for `3, 5, 13`.
4. **Congruences** (`run`, `kill`, `certs`). That leaves 113 prime sets. For each one a
   certificate, replayed by the kernel (`certs_ok`, `decide +kernel`), rules out every exponent vector:
   for any modulus `r`, `σ(q^(2e)) mod r` and `q^(2e) mod r` are periodic in `e`, so
   `1 + ∏ σ = 2 ∏ q^(2e)` can be tested on residue classes of the exponents. A certificate is a
   list of stages, each refining the periods and filtering the surviving residue classes with a few
   moduli; the soundness of the checker is proved once (`run_sound`).

Example: for `3, 5, 11, 71` every prime other than `3` is `≡ 2 (mod 3)`, so modulo `3` the
equation reads `1 + 1 ≡ 0`, which is false.
-/
namespace AAP4

open Finset

/-- `1 + q + ⋯ + q^(n-1)` in closed form (cheap for the kernel). -/
def gs (q n : ℕ) : ℕ := (q ^ n - 1) / (q - 1)

theorem gs_eq {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : gs q n = ∑ i ∈ range n, q ^ i :=
  (Nat.geomSum_eq hq n).symm

/-- Geometric sums are periodic modulo `m` once a full period sums to a multiple of `m`. -/
theorem geom_mod_period (x m T : ℕ) (hT : 0 < T) (hdvd : m ∣ ∑ i ∈ range T, x ^ i) (n : ℕ) :
    (∑ i ∈ range n, x ^ i) ≡ (∑ i ∈ range (n % T), x ^ i) [MOD m] := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < T
    · rw [Nat.mod_eq_of_lt hn]
    · obtain ⟨t, rfl⟩ : ∃ t, n = t + T := ⟨n - T, by omega⟩
      obtain ⟨j, hj⟩ := hdvd
      have hsplit : ∑ i ∈ range (t + T), x ^ i =
          ∑ i ∈ range t, x ^ i + m * (x ^ t * j) := by
        rw [Finset.sum_range_add]
        congr 1
        rw [show m * (x ^ t * j) = x ^ t * (m * j) by ring, ← hj, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [pow_add]
      unfold Nat.ModEq
      rw [hsplit, Nat.add_mul_mod_self_left, Nat.add_mod_right]
      exact ih t (by omega)

/-- `1 + x + ⋯ + x^n ≡ 1 (mod x)`. -/
theorem geom_mod_self (x n : ℕ) : (∑ i ∈ range (n + 1), x ^ i) ≡ 1 [MOD x] := by
  rw [Finset.sum_range_succ', pow_zero]
  have : ∑ i ∈ range n, x ^ (i + 1) = x * ∑ i ∈ range n, x ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [this]
  unfold Nat.ModEq
  simp [Nat.add_mod]

/-- `1 + x + ⋯ + x^(n+1) ≡ 1 + x (mod x²)`. -/
theorem geom_mod_sq (x n : ℕ) : (∑ i ∈ range (n + 2), x ^ i) ≡ 1 + x [MOD x * x] := by
  rw [Finset.sum_range_succ', Finset.sum_range_succ', pow_zero]
  have : ∑ i ∈ range n, x ^ (i + 1 + 1) = x * x * ∑ i ∈ range n, x ^ i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [this, zero_add, pow_one]
  unfold Nat.ModEq
  rw [show x * x * ∑ i ∈ range n, x ^ i + x + 1 = 1 + x + x * x * ∑ i ∈ range n, x ^ i by ring,
    Nat.add_mul_mod_self_left]

/-! ### The checker -/

/-- `∏ (1 + q_i + ⋯ + q_i^(2 y_i))` over paired lists. -/
def pG : List ℕ → List ℕ → ℕ
  | q :: qs, y :: ys => gs q (2 * y + 1) * pG qs ys
  | _, _ => 1

/-- `∏ q_i^(2 y_i)` over paired lists. -/
def pP : List ℕ → List ℕ → ℕ
  | q :: qs, y :: ys => q ^ (2 * y) * pP qs ys
  | _, _ => 1

/-- Residues `(e_i - 1) mod L_i` of the exponents. -/
def res : List ℕ → List ℕ → List ℕ
  | L :: Ls, e :: es => ((e - 1) % L) :: res Ls es
  | _, _ => []

/-- Representative exponents `(t_i mod T_i) + 1`. -/
def reps : List ℕ → List ℕ → List ℕ
  | t :: ts, T :: Ts => (t % T + 1) :: reps ts Ts
  | _, _ => []

/-- All residues modulo `L'` above the residue `t` modulo `L`. -/
def expand1 (L L' t : ℕ) : List ℕ := (List.range (L' / L)).map (fun j => t + L * j)

def expand : List ℕ → List ℕ → List ℕ → List (List ℕ)
  | L :: Ls, L' :: Ls', t :: ts =>
      (expand1 L L' t).flatMap (fun u => (expand Ls Ls' ts).map (u :: ·))
  | _, _, _ => [[]]

/-- The equation `1 + cs ∏ σ = 2 cx ∏ q^(2e)` modulo `r`, at the representative exponents. -/
def okAt (qs : List ℕ) (cs cx r : ℕ) (Ts ts : List ℕ) : Bool :=
  (1 + cs * pG qs (reps ts Ts)) % r == (2 * cx * pP qs (reps ts Ts)) % r

/-- `L_i ∣ L'_i`, all nonzero, same length. -/
def divB : List ℕ → List ℕ → Bool
  | L :: Ls, L' :: Ls' => L' % L == 0 && L != 0 && L' != 0 && divB Ls Ls'
  | [], [] => true
  | _, _ => false

/-- The modulus `r` is compatible with periods `T_i ∣ L_i`. -/
def validB (r : ℕ) : List ℕ → List ℕ → List ℕ → Bool
  | q :: qs, L :: Ls, T :: Ts =>
      Nat.ble 2 q && T != 0 && L % T == 0 &&
        (gs q (2 * T) % r == 0 || r == q || r == q * q) && validB r qs Ls Ts
  | [], [], [] => true
  | _, _, _ => false

abbrev Stage := List ℕ × List (ℕ × List ℕ)

def run (qs : List ℕ) (cs cx : ℕ) : List ℕ → List (List ℕ) → List Stage → Bool
  | _, surv, [] => surv.isEmpty
  | Ls, surv, (Ls', M) :: rest =>
      divB Ls Ls' && M.all (fun m => validB m.1 qs Ls' m.2) &&
        run qs cs cx Ls'
          ((surv.flatMap (expand Ls Ls')).filter (fun t => M.all (fun m => okAt qs cs cx m.1 m.2 t)))
          rest

/-! ### Soundness -/

theorem expand1_mem {L L' : ℕ} (hL : L ∣ L') (hL' : L' ≠ 0) (n : ℕ) :
    n % L' ∈ expand1 L L' (n % L) := by
  unfold expand1
  rw [List.mem_map]
  refine ⟨n % L' / L, ?_, ?_⟩
  · rw [List.mem_range]
    exact Nat.div_lt_div_of_lt_of_dvd hL (Nat.mod_lt _ (Nat.pos_of_ne_zero hL'))
  · have h1 := Nat.mod_mod_of_dvd n hL
    have h2 := Nat.div_add_mod (n % L') L
    rw [h1] at h2
    linarith

theorem expand_mem : ∀ (Ls Ls' es : List ℕ), divB Ls Ls' = true → es.length = Ls.length →
    res Ls' es ∈ expand Ls Ls' (res Ls es)
  | [], [], [], _, _ => by simp [res, expand]
  | [], [], _ :: _, _, h => by simp at h
  | L :: Ls, L' :: Ls', e :: es, hd, hl => by
      simp only [divB, Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at hd
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := hd
      simp only [res, expand, List.mem_flatMap, List.mem_map]
      refine ⟨(e - 1) % L', expand1_mem (Nat.dvd_of_mod_eq_zero h1) h3 _, _,
        expand_mem Ls Ls' es h4 (by simpa using hl), rfl⟩
  | L :: Ls, [], _, hd, _ => by simp [divB] at hd
  | [], _ :: _, _, hd, _ => by simp [divB] at hd
  | L :: Ls, L' :: Ls', [], _, hl => by simp at hl

/-- One prime: the residues of `σ(q^(2e))` and `q^(2e)` modulo `r` only depend on
`(e - 1) mod T`. -/
theorem prime_transfer {q L T r e : ℕ} (hq : 2 ≤ q) (hT : T ≠ 0) (hLT : L % T = 0)
    (hr : gs q (2 * T) % r = 0 ∨ r = q ∨ r = q * q) (he : 1 ≤ e) :
    gs q (2 * e + 1) ≡ gs q (2 * ((e - 1) % L % T + 1) + 1) [MOD r] ∧
      q ^ (2 * e) ≡ q ^ (2 * ((e - 1) % L % T + 1)) [MOD r] := by
  have hmm : (e - 1) % L % T = (e - 1) % T := Nat.mod_mod_of_dvd _ (Nat.dvd_of_mod_eq_zero hLT)
  rw [hmm]
  set y := (e - 1) % T + 1 with hy
  have hy1 : 1 ≤ y := by omega
  rw [gs_eq hq, gs_eq hq]
  rcases hr with hr | hr | hr
  · rw [gs_eq hq] at hr
    have hdvd : r ∣ ∑ i ∈ range (2 * T), q ^ i := Nat.dvd_of_mod_eq_zero hr
    have hT2 : 0 < 2 * T := by omega
    have hey : e ≡ y [MOD T] := by
      have := ((Nat.mod_modEq (e - 1) T).symm).add_right 1
      rwa [Nat.sub_add_cancel he] at this
    have h2 : 2 * e ≡ 2 * y [MOD 2 * T] := hey.mul_left' 2
    have h3 : 2 * e + 1 ≡ 2 * y + 1 [MOD 2 * T] := h2.add_right 1
    have pA := geom_mod_period q r (2 * T) hT2 hdvd (2 * e + 1)
    have pB := geom_mod_period q r (2 * T) hT2 hdvd (2 * y + 1)
    have pC := geom_mod_period q r (2 * T) hT2 hdvd (2 * e)
    have pD := geom_mod_period q r (2 * T) hT2 hdvd (2 * y)
    rw [show (2 * e + 1) % (2 * T) = (2 * y + 1) % (2 * T) from h3] at pA
    rw [show (2 * e) % (2 * T) = (2 * y) % (2 * T) from h2] at pC
    have hsum : ∑ i ∈ range (2 * e + 1), q ^ i ≡ ∑ i ∈ range (2 * y + 1), q ^ i [MOD r] :=
      pA.trans pB.symm
    refine ⟨hsum, ?_⟩
    have hsum' : ∑ i ∈ range (2 * e), q ^ i ≡ ∑ i ∈ range (2 * y), q ^ i [MOD r] :=
      pC.trans pD.symm
    rw [Finset.sum_range_succ, Finset.sum_range_succ] at hsum
    exact Nat.ModEq.add_left_cancel hsum' hsum
  · rw [hr]
    refine ⟨(geom_mod_self q (2 * e)).trans (geom_mod_self q (2 * y)).symm, ?_⟩
    unfold Nat.ModEq
    rw [Nat.mod_eq_zero_of_dvd (dvd_pow_self q (by omega)),
      Nat.mod_eq_zero_of_dvd (dvd_pow_self q (by omega))]
  · rw [hr]
    refine ⟨?_, ?_⟩
    · have a := geom_mod_sq q (2 * e - 1)
      have b := geom_mod_sq q (2 * y - 1)
      rw [show 2 * e - 1 + 2 = 2 * e + 1 by omega] at a
      rw [show 2 * y - 1 + 2 = 2 * y + 1 by omega] at b
      exact a.trans b.symm
    · have hd : ∀ n, 1 ≤ n → q * q ∣ q ^ (2 * n) := fun n hn => by
        rw [pow_mul, ← sq]
        exact dvd_pow_self _ (by omega)
      unfold Nat.ModEq
      rw [Nat.mod_eq_zero_of_dvd (hd e he), Nat.mod_eq_zero_of_dvd (hd y hy1)]

@[simp] theorem pG_nil (ys : List ℕ) : pG [] ys = 1 := rfl
@[simp] theorem pP_nil (ys : List ℕ) : pP [] ys = 1 := rfl
@[simp] theorem pG_cons (q y : ℕ) (qs ys : List ℕ) :
    pG (q :: qs) (y :: ys) = gs q (2 * y + 1) * pG qs ys := rfl
@[simp] theorem pP_cons (q y : ℕ) (qs ys : List ℕ) :
    pP (q :: qs) (y :: ys) = q ^ (2 * y) * pP qs ys := rfl
@[simp] theorem res_cons (L e : ℕ) (Ls es : List ℕ) :
    res (L :: Ls) (e :: es) = ((e - 1) % L) :: res Ls es := rfl
@[simp] theorem reps_cons (t T : ℕ) (ts Ts : List ℕ) :
    reps (t :: ts) (T :: Ts) = (t % T + 1) :: reps ts Ts := rfl

theorem list_transfer (r : ℕ) (qs : List ℕ) : ∀ (Ls Ts es : List ℕ), validB r qs Ls Ts = true →
    es.length = qs.length → (∀ e ∈ es, 1 ≤ e) →
    pG qs es ≡ pG qs (reps (res Ls es) Ts) [MOD r] ∧
      pP qs es ≡ pP qs (reps (res Ls es) Ts) [MOD r] := by
  induction qs with
  | nil =>
    intro Ls Ts es _ _ _
    exact ⟨rfl, rfl⟩
  | cons q qs ih =>
    intro Ls Ts es hv hl he
    match Ls, Ts, es, hv, hl with
    | L :: Ls, T :: Ts, e :: es, hv, hl =>
      simp only [validB, Bool.and_eq_true, Nat.ble_eq, bne_iff_ne, ne_eq, beq_iff_eq,
        Bool.or_eq_true] at hv
      obtain ⟨⟨⟨⟨h2, hT⟩, hLT⟩, hr⟩, hv'⟩ := hv
      have ih' := ih Ls Ts es hv' (by simpa using hl) (fun x hx => he x (by simp [hx]))
      have pt := prime_transfer (L := L) h2 hT hLT (by tauto) (he e (by simp))
      simp only [res_cons, reps_cons, pG_cons, pP_cons]
      exact ⟨pt.1.mul ih'.1, pt.2.mul ih'.2⟩
    | [], _, _, hv, _ => simp [validB] at hv
    | _ :: _, [], _, hv, _ => simp [validB] at hv
    | _ :: _, _ :: _, [], _, hl => simp at hl

theorem divB_length : ∀ (Ls Ls' : List ℕ), divB Ls Ls' = true → Ls'.length = Ls.length
  | [], [], _ => rfl
  | _ :: Ls, _ :: Ls', h => by
      simp only [divB, Bool.and_eq_true] at h
      simp [divB_length Ls Ls' h.2]
  | [], _ :: _, h => by simp [divB] at h
  | _ :: _, [], h => by simp [divB] at h

theorem run_sound (qs : List ℕ) (cs cx : ℕ) (es : List ℕ) (hl : es.length = qs.length)
    (he : ∀ e ∈ es, 1 ≤ e) (h : 1 + cs * pG qs es = 2 * cx * pP qs es) :
    ∀ (stages : List Stage) (Ls : List ℕ) (surv : List (List ℕ)), Ls.length = qs.length →
      res Ls es ∈ surv → run qs cs cx Ls surv stages = true → False := by
  intro stages
  induction stages with
  | nil =>
    intro Ls surv _ hmem hrun
    simp only [run, List.isEmpty_iff] at hrun
    subst hrun
    simp at hmem
  | cons st rest ih =>
    obtain ⟨Ls', M⟩ := st
    intro Ls surv hLs hmem hrun
    simp only [run, Bool.and_eq_true, List.all_eq_true] at hrun
    obtain ⟨⟨hdiv, hval⟩, hrest⟩ := hrun
    have hLs' : Ls'.length = qs.length := (divB_length Ls Ls' hdiv).trans hLs
    refine ih Ls' _ hLs' ?_ hrest
    rw [List.mem_filter, List.mem_flatMap]
    refine ⟨⟨res Ls es, hmem, expand_mem Ls Ls' es hdiv (by rw [hl, hLs])⟩, ?_⟩
    rw [List.all_eq_true]
    intro m hm
    have tr := list_transfer m.1 qs Ls' m.2 es (hval m hm) hl he
    simp only [okAt, beq_iff_eq]
    have a1 := Nat.ModEq.add_left 1 (tr.1.mul_left cs)
    have a2 := tr.2.mul_left (2 * cx)
    unfold Nat.ModEq at a1 a2
    rw [← a1, ← a2, h]

theorem res_ones : ∀ (qs es : List ℕ), es.length = qs.length →
    res (qs.map fun _ => 1) es = qs.map fun _ => 0
  | [], [], _ => rfl
  | _ :: qs, _ :: es, h => by
      simp only [List.map_cons, res_cons, Nat.mod_one, List.cons.injEq, true_and]
      exact res_ones qs es (by simpa using h)
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- A successful run of the checker rules out every exponent vector. -/
theorem kill (qs : List ℕ) (cs cx : ℕ) (stages : List Stage)
    (hrun : run qs cs cx (qs.map fun _ => 1) [qs.map fun _ => 0] stages = true)
    (es : List ℕ) (hl : es.length = qs.length) (he : ∀ e ∈ es, 1 ≤ e)
    (h : 1 + cs * pG qs es = 2 * cx * pP qs es) : False :=
  run_sound qs cs cx es hl he h stages _ _ (by simp) (by rw [res_ones qs es hl]; simp) hrun


/-- Congruence certificates: for each prime set, the stages of the sieve. -/
def certs : List (List ℕ × List Stage) := [
  ([3, 5, 11, 13],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 1, 6], [(4, [1, 2, 1, 2])]), ([3, 2, 6, 6], [(13, [3, 2, 6, 1])]), ([3, 6, 6, 6], [(7, [3, 3, 3, 1])]), ([3, 6, 6, 18], [(9, [1, 3, 3, 9])]), ([9, 18, 6, 18], [(19, [9, 9, 3, 9]), (37, [9, 18, 3, 18])])]),
  ([3, 5, 11, 17],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 19],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 2, 5, 3], [(5, [2, 1, 5, 1])]), ([6, 2, 30, 6], [(13, [3, 2, 6, 6])]), ([6, 4, 30, 6], [(8, [2, 4, 2, 2])]), ([6, 12, 30, 6], [(7, [3, 3, 3, 3])]), ([18, 36, 30, 6], [(19, [9, 9, 3, 1])])]),
  ([3, 5, 11, 23],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 29],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 31],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([3, 2, 6, 6], [(13, [3, 2, 6, 2])]), ([3, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([9, 18, 6, 6], [(19, [9, 9, 3, 3]), (37, [9, 18, 3, 2])])]),
  ([3, 5, 11, 37],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 1, 6], [(4, [1, 2, 1, 2])]), ([3, 2, 6, 6], [(13, [3, 2, 6, 6])]), ([3, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([9, 18, 6, 6], [(19, [9, 9, 3, 1]), (37, [9, 18, 3, 1])])]),
  ([3, 5, 11, 41],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 43],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([5, 10, 1, 3], [(11, [5, 5, 1, 1])])]),
  ([3, 5, 11, 47],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 53],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 59],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 61],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 1, 6], [(4, [1, 2, 1, 2])]), ([3, 2, 6, 6], [(13, [3, 2, 6, 3])]), ([3, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([3, 6, 6, 18], [(9, [1, 3, 3, 9])]), ([9, 18, 6, 18], [(19, [9, 9, 3, 9])])]),
  ([3, 5, 11, 67],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 2, 5, 6], [(5, [2, 1, 5, 2])]), ([2, 4, 10, 6], [(8, [2, 4, 2, 2])]), ([6, 4, 30, 6], [(13, [3, 2, 6, 6])]), ([6, 12, 30, 6], [(7, [3, 3, 3, 3])]), ([30, 12, 30, 6], [(31, [15, 3, 15, 3])])]),
  ([3, 5, 11, 71],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 73],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 1, 6], [(4, [1, 2, 1, 2])]), ([3, 2, 6, 6], [(13, [3, 2, 6, 2])]), ([3, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([3, 6, 6, 18], [(9, [1, 3, 3, 9])]), ([9, 18, 6, 18], [(19, [9, 9, 3, 9]), (37, [9, 18, 3, 1])])]),
  ([3, 5, 11, 79],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 2, 5, 3], [(5, [2, 1, 5, 1])]), ([2, 4, 10, 3], [(8, [2, 4, 2, 1])]), ([4, 8, 20, 3], [(16, [4, 8, 4, 1])]), ([4, 40, 20, 12], [(41, [4, 10, 20, 4])]), ([8, 40, 40, 24], [(17, [8, 8, 8, 8])]), ([8, 80, 40, 24], [(32, [8, 16, 8, 2])]), ([24, 240, 120, 24], [(7, [3, 3, 3, 3]), (97, [24, 48, 24, 8])]), ([24, 240, 120, 72], [(9, [1, 3, 3, 9])]), ([72, 720, 120, 72], [(19, [9, 9, 3, 9]), (37, [9, 18, 3, 18])])]),
  ([3, 5, 11, 83],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 89],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 97],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 1, 6], [(4, [1, 2, 1, 2])]), ([3, 2, 6, 6], [(13, [3, 2, 6, 6])]), ([3, 6, 6, 6], [(7, [3, 3, 3, 1])]), ([9, 18, 6, 6], [(37, [9, 18, 3, 6])])]),
  ([3, 5, 11, 101],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 103],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([3, 2, 6, 3], [(13, [3, 2, 6, 1])]), ([3, 6, 6, 3], [(7, [3, 3, 3, 3])])]),
  ([3, 5, 11, 107],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 109],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 1, 6], [(4, [1, 2, 1, 2])]), ([5, 10, 1, 6], [(11, [5, 5, 1, 1])])]),
  ([3, 5, 11, 113],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 127],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([3, 2, 6, 3], [(13, [3, 2, 6, 3])])]),
  ([3, 5, 11, 131],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 137],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 11, 139],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([3, 2, 6, 3], [(13, [3, 2, 6, 3])]), ([3, 6, 6, 3], [(7, [3, 3, 3, 1])]), ([3, 6, 6, 9], [(9, [1, 3, 3, 9])]), ([9, 18, 6, 9], [(19, [9, 9, 3, 9])])]),
  ([3, 5, 13, 17],
    [([1, 1, 3, 1], [(3, [1, 1, 3, 1])]), ([2, 1, 6, 2], [(5, [2, 1, 2, 2])]), ([2, 2, 6, 2], [(4, [1, 2, 2, 2])]), ([6, 2, 6, 6], [(13, [3, 2, 1, 3])])]),
  ([3, 5, 13, 19],
    [([2, 1, 2, 1], [(5, [2, 1, 2, 1])]), ([2, 2, 2, 1], [(4, [1, 2, 2, 1])]), ([6, 2, 2, 6], [(13, [3, 2, 1, 6])])]),
  ([3, 5, 13, 23],
    [([1, 1, 3, 1], [(3, [1, 1, 3, 1])]), ([3, 2, 3, 3], [(13, [3, 2, 1, 3])])]),
  ([3, 5, 13, 29],
    [([1, 1, 3, 1], [(3, [1, 1, 3, 1])]), ([2, 1, 6, 1], [(5, [2, 1, 2, 1])]), ([6, 2, 6, 3], [(13, [3, 2, 1, 3])])]),
  ([3, 5, 13, 31],
    [([3, 2, 1, 2], [(13, [3, 2, 1, 2])]), ([3, 2, 2, 2], [(4, [1, 2, 2, 1])]), ([3, 2, 6, 6], [(3, [1, 1, 3, 3])]), ([3, 6, 6, 6], [(7, [3, 3, 1, 3])]), ([9, 18, 18, 6], [(19, [9, 9, 9, 3]), (37, [9, 18, 18, 2])])]),
  ([3, 5, 13, 37],
    [([2, 1, 2, 2], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 2], [(4, [1, 2, 2, 2])]), ([6, 2, 2, 6], [(13, [3, 2, 1, 6])]), ([6, 2, 6, 6], [(3, [1, 1, 3, 3])]), ([6, 6, 6, 6], [(7, [3, 3, 1, 3])]), ([30, 6, 30, 6], [(31, [15, 3, 15, 3])])]),
  ([3, 5, 13, 41],
    [([1, 1, 3, 1], [(3, [1, 1, 3, 1])]), ([3, 3, 3, 1], [(7, [3, 3, 1, 1])]), ([3, 6, 3, 6], [(13, [3, 2, 1, 6])]), ([3, 6, 6, 6], [(4, [1, 2, 2, 2])]), ([3, 6, 18, 6], [(9, [1, 3, 9, 3])]), ([9, 18, 18, 18], [(19, [9, 9, 9, 9]), (37, [9, 18, 18, 9])])]),
  ([3, 5, 13, 43],
    [([1, 2, 2, 1], [(4, [1, 2, 2, 1])]), ([3, 2, 2, 3], [(13, [3, 2, 1, 3])]), ([3, 2, 6, 3], [(3, [1, 1, 3, 3])]), ([6, 2, 6, 6], [(5, [2, 1, 2, 2])]), ([6, 4, 12, 6], [(8, [2, 4, 4, 2])]), ([24, 8, 12, 12], [(17, [8, 8, 2, 4])]), ([24, 8, 24, 12], [(16, [4, 8, 8, 4])]), ([24, 48, 48, 12], [(97, [24, 48, 48, 12])])]),
  ([3, 5, 17, 19],
    [([2, 1, 2, 1], [(5, [2, 1, 2, 1])])]),
  ([3, 5, 17, 23],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 29],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 31],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 2, 3], [(4, [1, 2, 2, 1])]), ([2, 2, 2, 15], [(5, [2, 1, 2, 5])]), ([2, 4, 4, 15], [(8, [2, 4, 4, 1])]), ([6, 4, 12, 30], [(13, [3, 2, 3, 2])]), ([6, 12, 12, 30], [(7, [3, 3, 3, 3])]), ([6, 12, 12, 90], [(9, [1, 3, 1, 9])]), ([6, 36, 12, 180], [(73, [6, 36, 12, 36])]), ([18, 36, 36, 180], [(19, [9, 9, 9, 3])])]),
  ([3, 5, 17, 37],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 2])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 6])]), ([6, 6, 6, 6], [(7, [3, 3, 3, 3])])]),
  ([3, 5, 17, 41],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 43],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 1])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 3])]), ([6, 4, 12, 6], [(8, [2, 4, 4, 2])]), ([6, 36, 12, 12], [(73, [6, 36, 12, 12])]), ([6, 36, 12, 36], [(9, [1, 3, 1, 9])]), ([18, 36, 36, 36], [(19, [9, 9, 9, 9])])]),
  ([3, 5, 17, 47],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 53],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 59],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 61],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([3, 2, 3, 3], [(13, [3, 2, 3, 3])]), ([3, 6, 3, 3], [(7, [3, 3, 3, 3])]), ([3, 6, 3, 9], [(9, [1, 3, 1, 9])]), ([3, 6, 6, 18], [(4, [1, 2, 2, 2])]), ([9, 18, 18, 18], [(19, [9, 9, 9, 9]), (37, [9, 18, 18, 18])])]),
  ([3, 5, 17, 67],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 1])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 6])])]),
  ([3, 5, 17, 71],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 73],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 2])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 2])]), ([6, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([6, 36, 12, 6], [(73, [6, 36, 12, 1])])]),
  ([3, 5, 17, 79],
    [([2, 1, 2, 1], [(5, [2, 1, 2, 1])])]),
  ([3, 5, 17, 83],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 89],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 97],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 2])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 6])]), ([6, 6, 6, 6], [(7, [3, 3, 3, 1])]), ([6, 36, 12, 6], [(73, [6, 36, 12, 6])])]),
  ([3, 5, 17, 101],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 103],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 1])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 1])]), ([6, 6, 6, 6], [(7, [3, 3, 3, 3])])]),
  ([3, 5, 17, 107],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 109],
    [([2, 1, 2, 1], [(5, [2, 1, 2, 1])])]),
  ([3, 5, 17, 113],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 127],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 1])]), ([2, 4, 4, 6], [(8, [2, 4, 4, 1])]), ([8, 8, 4, 12], [(17, [8, 8, 1, 4])]), ([8, 8, 8, 12], [(16, [4, 8, 8, 1])]), ([8, 16, 16, 12], [(32, [8, 16, 16, 1])]), ([24, 16, 48, 12], [(13, [3, 2, 3, 3])]), ([24, 48, 48, 48], [(97, [24, 48, 48, 16])]), ([24, 96, 96, 96], [(193, [8, 96, 96, 96])])]),
  ([3, 5, 17, 131],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 137],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 139],
    [([2, 1, 2, 1], [(5, [2, 1, 2, 1])])]),
  ([3, 5, 17, 149],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 151],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 2, 3], [(4, [1, 2, 2, 1])]), ([2, 2, 2, 15], [(5, [2, 1, 2, 5])]), ([2, 4, 4, 15], [(8, [2, 4, 4, 1])]), ([6, 4, 12, 30], [(13, [3, 2, 3, 2])]), ([6, 12, 12, 30], [(7, [3, 3, 3, 3])]), ([6, 12, 12, 90], [(9, [1, 3, 1, 9])]), ([6, 36, 12, 180], [(73, [6, 36, 12, 36])]), ([18, 36, 36, 180], [(19, [9, 9, 9, 1])])]),
  ([3, 5, 17, 157],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 2])]), ([8, 8, 2, 6], [(17, [8, 8, 1, 2])])]),
  ([3, 5, 17, 163],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 1])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 6])]), ([6, 6, 6, 6], [(7, [3, 3, 3, 3])])]),
  ([3, 5, 17, 167],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 173],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 179],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 181],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([3, 2, 3, 3], [(13, [3, 2, 3, 1])]), ([3, 6, 3, 3], [(7, [3, 3, 3, 1])]), ([3, 6, 3, 9], [(9, [1, 3, 1, 9])]), ([3, 6, 6, 18], [(4, [1, 2, 2, 2])]), ([15, 6, 30, 18], [(31, [15, 3, 15, 3])])]),
  ([3, 5, 17, 191],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 193],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 2])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 6])]), ([6, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([6, 6, 6, 18], [(9, [1, 3, 1, 9])]), ([6, 36, 12, 36], [(8, [2, 4, 4, 4]), (73, [6, 36, 12, 36])])]),
  ([3, 5, 17, 197],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 199],
    [([2, 1, 2, 1], [(5, [2, 1, 2, 1])])]),
  ([3, 5, 17, 211],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 2, 3], [(4, [1, 2, 2, 1])]), ([3, 2, 6, 3], [(13, [3, 2, 3, 3])]), ([6, 2, 6, 15], [(5, [2, 1, 2, 5])]), ([6, 36, 12, 15], [(73, [6, 36, 12, 3])])]),
  ([3, 5, 17, 223],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 2, 1])]), ([2, 4, 4, 6], [(8, [2, 4, 4, 1])]), ([8, 8, 4, 12], [(17, [8, 8, 1, 4])]), ([8, 8, 8, 12], [(16, [4, 8, 8, 1])]), ([8, 16, 16, 12], [(32, [8, 16, 16, 1])]), ([24, 16, 48, 12], [(13, [3, 2, 3, 6])]), ([24, 48, 48, 12], [(7, [3, 3, 3, 1])]), ([24, 48, 48, 48], [(97, [24, 48, 48, 48])])]),
  ([3, 5, 17, 227],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 229],
    [([2, 1, 2, 1], [(5, [2, 1, 2, 1])])]),
  ([3, 5, 17, 233],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 239],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 17, 241],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 3, 1, 9], [(9, [1, 3, 1, 9])]), ([3, 3, 3, 9], [(7, [3, 3, 3, 3])]), ([3, 6, 3, 18], [(13, [3, 2, 3, 6])])]),
  ([3, 5, 17, 251],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 19, 23],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 3, 1], [(3, [1, 1, 3, 1])]), ([2, 2, 3, 2], [(5, [2, 1, 1, 2])]), ([6, 2, 6, 6], [(13, [3, 2, 6, 3])])]),
  ([3, 5, 19, 29],
    [([2, 1, 1, 1], [(5, [2, 1, 1, 1])])]),
  ([3, 5, 19, 31],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 3, 3], [(3, [1, 1, 3, 3])]), ([3, 6, 3, 3], [(7, [3, 3, 3, 3])]), ([3, 6, 6, 6], [(13, [3, 2, 6, 2])]), ([9, 18, 6, 6], [(19, [9, 9, 1, 3])]), ([9, 18, 18, 6], [(37, [9, 18, 18, 2])])]),
  ([3, 5, 19, 37],
    [([2, 1, 1, 2], [(5, [2, 1, 1, 2])])]),
  ([3, 5, 19, 41],
    [([1, 1, 3, 1], [(3, [1, 1, 3, 1])]), ([3, 3, 3, 1], [(7, [3, 3, 3, 1])]), ([3, 6, 3, 2], [(4, [1, 2, 1, 2])]), ([3, 6, 6, 6], [(13, [3, 2, 6, 6])]), ([3, 6, 18, 6], [(9, [1, 3, 9, 3])]), ([9, 18, 18, 18], [(19, [9, 9, 1, 9]), (37, [9, 18, 18, 9])])]),
  ([3, 5, 19, 43],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([2, 2, 1, 2], [(5, [2, 1, 1, 2])]), ([2, 4, 2, 2], [(8, [2, 4, 2, 2])]), ([6, 4, 6, 6], [(3, [1, 1, 3, 3]), (13, [3, 2, 6, 3])])]),
  ([3, 5, 19, 47],
    [([2, 1, 1, 2], [(5, [2, 1, 1, 2])])]),
  ([3, 5, 19, 53],
    [([1, 1, 3, 1], [(3, [1, 1, 3, 1])]), ([2, 1, 3, 2], [(5, [2, 1, 1, 2])]), ([2, 2, 3, 2], [(4, [1, 2, 1, 2])]), ([2, 6, 9, 2], [(9, [1, 3, 9, 1])]), ([6, 6, 9, 6], [(7, [3, 3, 3, 3])]), ([6, 6, 18, 78], [(13, [3, 2, 6, 13])]), ([6, 12, 18, 156], [(8, [2, 4, 2, 4])]), ([6, 36, 18, 468], [(73, [6, 36, 18, 36])]), ([18, 36, 18, 468], [(19, [9, 9, 1, 9]), (37, [9, 18, 18, 9])])]),
  ([3, 5, 19, 59],
    [([2, 1, 1, 1], [(5, [2, 1, 1, 1])])]),
  ([3, 5, 19, 61],
    [([1, 2, 1, 2], [(4, [1, 2, 1, 2])]), ([1, 2, 3, 6], [(3, [1, 1, 3, 3])]), ([3, 2, 6, 6], [(13, [3, 2, 6, 3])]), ([3, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([6, 6, 6, 30], [(5, [2, 1, 1, 5])]), ([6, 12, 6, 60], [(8, [2, 4, 2, 4])]), ([6, 36, 18, 180], [(9, [1, 3, 9, 9]), (73, [6, 36, 18, 18])]), ([18, 36, 18, 180], [(19, [9, 9, 1, 9])])]),
  ([3, 5, 19, 67],
    [([2, 1, 1, 2], [(5, [2, 1, 1, 2])])]),
  ([3, 5, 19, 71],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 3, 1], [(3, [1, 1, 3, 1])]), ([2, 2, 3, 5], [(5, [2, 1, 1, 5])]), ([2, 4, 6, 5], [(8, [2, 4, 2, 1])]), ([6, 4, 6, 30], [(13, [3, 2, 6, 6])]), ([6, 12, 18, 30], [(9, [1, 3, 9, 1])]), ([6, 36, 18, 90], [(73, [6, 36, 18, 9])])]),
  ([3, 5, 19, 73],
    [([2, 1, 1, 2], [(5, [2, 1, 1, 2])]), ([2, 2, 1, 2], [(4, [1, 2, 1, 2])]), ([6, 2, 6, 2], [(13, [3, 2, 6, 2])]), ([6, 2, 6, 6], [(3, [1, 1, 3, 3])]), ([6, 6, 6, 6], [(7, [3, 3, 3, 3])]), ([6, 36, 18, 6], [(73, [6, 36, 18, 1])])]),
  ([3, 5, 19, 79],
    [([2, 1, 1, 1], [(5, [2, 1, 1, 1])])]),
  ([3, 5, 19, 83],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 3, 1], [(3, [1, 1, 3, 1])]), ([2, 2, 3, 2], [(5, [2, 1, 1, 2])]), ([6, 2, 6, 2], [(13, [3, 2, 6, 2])]), ([6, 4, 6, 2], [(8, [2, 4, 2, 2])]), ([6, 12, 6, 2], [(7, [3, 3, 3, 1])]), ([6, 36, 18, 4], [(73, [6, 36, 18, 4])])]),
  ([3, 5, 19, 89],
    [([2, 1, 1, 1], [(5, [2, 1, 1, 1])])]),
  ([3, 5, 23, 29],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 23, 31],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 4, 1, 3], [(8, [2, 4, 1, 1])]), ([2, 4, 2, 15], [(5, [2, 1, 2, 5])]), ([4, 8, 2, 15], [(16, [4, 8, 2, 1])]), ([4, 40, 10, 15], [(41, [4, 10, 5, 5])]), ([20, 120, 10, 30], [(61, [5, 15, 10, 30])]), ([60, 120, 10, 30], [(31, [15, 3, 5, 1])])]),
  ([3, 5, 23, 37],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([2, 1, 2, 6], [(5, [2, 1, 2, 2])]), ([2, 2, 2, 6], [(4, [1, 2, 1, 2])]), ([6, 2, 6, 6], [(13, [3, 2, 3, 6])])]),
  ([3, 5, 23, 41],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 23, 43],
    [([1, 2, 1, 1], [(4, [1, 2, 1, 1])]), ([1, 2, 1, 3], [(3, [1, 1, 1, 3])]), ([3, 2, 3, 3], [(13, [3, 2, 3, 3])]), ([6, 2, 6, 6], [(5, [2, 1, 2, 2])]), ([6, 4, 6, 6], [(8, [2, 4, 1, 2])]), ([6, 12, 6, 18], [(9, [1, 3, 3, 9])]), ([18, 36, 6, 18], [(37, [9, 18, 6, 2])]), ([18, 36, 18, 18], [(19, [9, 9, 9, 9])])]),
  ([3, 5, 23, 47],
    [([1, 1, 1, 1], [(3, [1, 1, 1, 1])])]),
  ([3, 5, 29, 31],
    [([1, 1, 1, 3], [(3, [1, 1, 1, 3])]), ([1, 2, 2, 3], [(4, [1, 2, 2, 1])]), ([3, 2, 6, 6], [(13, [3, 2, 3, 2])]), ([6, 2, 6, 30], [(5, [2, 1, 1, 5])]), ([6, 4, 12, 30], [(8, [2, 4, 4, 1])]), ([18, 36, 12, 30], [(37, [9, 18, 6, 2])]), ([18, 36, 12, 90], [(9, [1, 3, 3, 9])]), ([18, 36, 36, 180], [(19, [9, 9, 9, 3]), (73, [6, 36, 36, 36])])]),
  ([3, 7, 11, 13],
    [([1, 1, 1, 2], [(4, [1, 1, 1, 2])]), ([3, 1, 3, 2], [(7, [3, 1, 3, 1])]), ([3, 6, 6, 2], [(13, [3, 6, 6, 1])])]),
  ([3, 7, 11, 17],
    [([1, 1, 1, 2], [(4, [1, 1, 1, 2])]), ([1, 3, 1, 2], [(3, [1, 3, 1, 1])]), ([1, 9, 3, 2], [(9, [1, 9, 3, 1])]), ([3, 9, 3, 6], [(7, [3, 1, 3, 3])]), ([9, 9, 3, 18], [(19, [9, 3, 3, 9]), (37, [9, 9, 3, 18])])]),
  ([3, 7, 11, 19],
    [([1, 3, 1, 3], [(3, [1, 3, 1, 3])]), ([3, 3, 3, 3], [(7, [3, 1, 3, 3])]), ([9, 3, 3, 3], [(19, [9, 3, 3, 1])])]),
  ([3, 7, 11, 23],
    [([1, 3, 1, 1], [(3, [1, 3, 1, 1])]), ([2, 3, 2, 1], [(8, [2, 1, 2, 1])]), ([6, 3, 6, 3], [(7, [3, 1, 3, 3])]), ([6, 6, 6, 3], [(13, [3, 6, 6, 3])]), ([18, 6, 6, 9], [(19, [9, 3, 3, 9])])]),
  ([3, 7, 13, 17],
    [([1, 1, 2, 2], [(4, [1, 1, 2, 2])]), ([1, 3, 6, 2], [(3, [1, 3, 3, 1])]), ([3, 6, 6, 6], [(7, [3, 1, 1, 3]), (13, [3, 6, 1, 3])])]),
  ([3, 7, 13, 19],
    [([1, 1, 2, 1], [(4, [1, 1, 2, 1])]), ([3, 1, 2, 3], [(7, [3, 1, 1, 3])]), ([3, 6, 2, 6], [(13, [3, 6, 1, 6])])])
]

/-- Every certificate in the table runs successfully (checked by the kernel). -/
theorem certs_ok : certs.all (fun x => run x.1 1 1 (x.1.map fun _ => 1) [x.1.map fun _ => 0] x.2)
    = true := by
  decide +kernel

/-- No listed prime set carries an odd almost perfect number. -/
theorem killKey (qs : List ℕ) (hq : qs ∈ certs.map Prod.fst) (a b c d : ℕ) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG qs [a, b, c, d] = 2 * pP qs [a, b, c, d]) : False := by
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hq
  have hrun := List.all_eq_true.1 certs_ok x hx
  have hlen : x.1.length = 4 := by
    have := List.all_eq_true.1 (show certs.all (fun y => y.1.length == 4) = true by decide +kernel) x hx
    simpa using this
  exact kill x.1 1 1 x.2 hrun [a, b, c, d] (by simp [hlen]) (by simp [ha, hb, hc, hd])
    (by simpa using h)

/-! ### One prime power -/

/-- `(q - 1) σ(q^(n-1)) + 1 = q^n`. -/
theorem gs_mul {q : ℕ} (hq : 2 ≤ q) (n : ℕ) : (q - 1) * gs q n + 1 = q ^ n := by
  rw [gs_eq hq]
  have := geom_sum_mul_add (q - 1) n
  rw [Nat.sub_add_cancel (by omega : 1 ≤ q)] at this
  rw [← this]
  ring

/-- The facts about `S = σ(q^(2e))` and `X = q^(2e)` used below, in `ℤ`. -/
theorem pfacts {q e : ℕ} (hq : 3 ≤ q) (he : 1 ≤ e) :
    ((q : ℤ) - 1) * (gs q (2 * e + 1) : ℤ) + 1 = (q : ℤ) * (q : ℤ) ^ (2 * e) ∧
      (q : ℤ) ^ 2 ≤ (q : ℤ) ^ (2 * e) := by
  constructor
  · have h := gs_mul (by omega : 2 ≤ q) (2 * e + 1)
    have h' := congrArg (fun n : ℕ => (n : ℤ)) h
    push_cast [Nat.cast_sub (by omega : 1 ≤ q)] at h'
    rw [h', pow_succ]
    ring
  · exact_mod_cast Nat.pow_le_pow_right (by omega) (by omega)

/-- `(q² + q + 1) X ≤ q² S`. -/
theorem lo2 (q S X : ℤ) (hq : 3 ≤ q) (e : (q - 1) * S + 1 = q * X) (hX : q ^ 2 ≤ X) :
    (q ^ 2 + q + 1) * X ≤ q ^ 2 * S := by
  have key : (q - 1) * (q ^ 2 * S - (q ^ 2 + q + 1) * X) = X - q ^ 2 := by
    linear_combination q ^ 2 * e
  have h0 : 0 ≤ (q - 1) * (q ^ 2 * S - (q ^ 2 + q + 1) * X) := by rw [key]; linarith
  nlinarith

/-- `(q⁴ + q³ + q² + q + 1) X ≤ q⁴ S` once `X ≥ q⁴`. -/
theorem lo4 (q S X : ℤ) (hq : 3 ≤ q) (e : (q - 1) * S + 1 = q * X) (hX : q ^ 4 ≤ X) :
    (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * X ≤ q ^ 4 * S := by
  have key : (q - 1) * (q ^ 4 * S - (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * X) = X - q ^ 4 := by
    linear_combination q ^ 4 * e
  have h0 : 0 ≤ (q - 1) * (q ^ 4 * S - (q ^ 4 + q ^ 3 + q ^ 2 + q + 1) * X) := by
    rw [key]; linarith
  nlinarith

theorem mul4_le (a0 a1 a2 a3 b0 b1 b2 b3 : ℤ) (h0 : a0 ≤ b0) (h1 : a1 ≤ b1) (h2 : a2 ≤ b2)
    (h3 : a3 ≤ b3) (n0 : 0 ≤ a0) (n1 : 0 ≤ a1) (n2 : 0 ≤ a2) (n3 : 0 ≤ a3) :
    a0 * a1 * a2 * a3 ≤ b0 * b1 * b2 * b3 := by
  have u := mul_le_mul h0 h1 n1 (n0.trans h0)
  have v := mul_le_mul u h2 n2 (mul_nonneg (n0.trans h0) (n1.trans h1))
  exact mul_le_mul v h3 n3 (mul_nonneg (mul_nonneg (n0.trans h0) (n1.trans h1)) (n2.trans h2))

theorem quartic_lt (y0 y1 y2 y3 : ℤ) (h0 : 1 ≤ y0) (h1 : 1 ≤ y1) (h2 : 1 ≤ y2) (h3 : 1 ≤ y3) :
    (y0 - 1) * (y1 - 1) * (y2 - 1) * (y3 - 1) < y0 * y1 * y2 * y3 := by
  have a := mul4_le (y0 - 1) (y1 - 1) (y2 - 1) (y3 - 1) y0 y1 y2 (y3 - 1) (by linarith)
    (by linarith) (by linarith) le_rfl (by linarith) (by linarith) (by linarith) (by linarith)
  have b : 1 ≤ y0 * y1 * y2 := by
    have := mul_le_mul h0 h1 zero_le_one (by linarith)
    have := mul_le_mul this h2 zero_le_one (by nlinarith)
    simpa using this
  nlinarith

/-! ### The abundancy bound `2 (p₀-1)(p₁-1)(p₂-1)(p₃-1) ≤ p₀ p₁ p₂ p₃` -/

theorem final_step (Q N K Am : ℤ) (E : Q * (2 * K - 1) = Am) (hlt : Am < N * K) (hQK : Q ≤ K)
    (hK : 0 ≤ K) : 2 * Q ≤ N := by
  by_contra hc
  have h1 : (0 : ℤ) ≤ 2 * Q - N - 1 := by omega
  nlinarith [mul_nonneg h1 hK]

theorem hi_bound (P0 P1 P2 P3 X0 X1 X2 X3 S0 S1 S2 S3 : ℤ)
    (hP0 : 3 ≤ P0) (hP1 : 3 ≤ P1) (hP2 : 3 ≤ P2) (hP3 : 3 ≤ P3)
    (hX0 : P0 ≤ X0) (hX1 : P1 ≤ X1) (hX2 : P2 ≤ X2) (hX3 : P3 ≤ X3)
    (e0 : (P0 - 1) * S0 + 1 = P0 * X0) (e1 : (P1 - 1) * S1 + 1 = P1 * X1)
    (e2 : (P2 - 1) * S2 + 1 = P2 * X2) (e3 : (P3 - 1) * S3 + 1 = P3 * X3)
    (h : 1 + S0 * S1 * S2 * S3 = 2 * (X0 * X1 * X2 * X3)) :
    2 * ((P0 - 1) * (P1 - 1) * (P2 - 1) * (P3 - 1)) ≤ P0 * P1 * P2 * P3 := by
  have E : (P0 - 1) * (P1 - 1) * (P2 - 1) * (P3 - 1) * (2 * (X0 * X1 * X2 * X3) - 1) =
      (P0 * X0 - 1) * (P1 * X1 - 1) * (P2 * X2 - 1) * (P3 * X3 - 1) := by
    linear_combination (-((P0 - 1) * (P1 - 1) * (P2 - 1) * (P3 - 1))) * h +
      ((P1 - 1) * S1 * ((P2 - 1) * S2) * ((P3 - 1) * S3)) * e0 +
      ((P0 * X0 - 1) * ((P2 - 1) * S2) * ((P3 - 1) * S3)) * e1 +
      ((P0 * X0 - 1) * (P1 * X1 - 1) * ((P3 - 1) * S3)) * e2 +
      ((P0 * X0 - 1) * (P1 * X1 - 1) * (P2 * X2 - 1)) * e3
  have hlt := quartic_lt (P0 * X0) (P1 * X1) (P2 * X2) (P3 * X3) (by nlinarith) (by nlinarith)
    (by nlinarith) (by nlinarith)
  have hQK := mul4_le (P0 - 1) (P1 - 1) (P2 - 1) (P3 - 1) X0 X1 X2 X3 (by linarith) (by linarith)
    (by linarith) (by linarith) (by linarith) (by linarith) (by linarith) (by linarith)
  have hK : 0 ≤ X0 * X1 * X2 * X3 := by
    have := mul4_le 0 0 0 0 X0 X1 X2 X3 (by linarith) (by linarith) (by linarith) (by linarith)
      le_rfl le_rfl le_rfl le_rfl
    simpa using this
  have hNK : P0 * X0 * (P1 * X1) * (P2 * X2) * (P3 * X3) =
      P0 * P1 * P2 * P3 * (X0 * X1 * X2 * X3) := by ring
  rw [hNK, ← E] at hlt
  generalize (P0 - 1) * (P1 - 1) * (P2 - 1) * (P3 - 1) = Q at hlt hQK ⊢
  generalize P0 * P1 * P2 * P3 = N at hlt ⊢
  generalize X0 * X1 * X2 * X3 = K at hlt hQK hK
  exact final_step Q N K _ rfl hlt hQK hK

theorem mono4 (x0 x1 x2 x3 c0 c1 c2 c3 : ℤ) (h0 : c0 ≤ x0) (h1 : c1 ≤ x1) (h2 : c2 ≤ x2)
    (h3 : c3 ≤ x3) (g0 : 2 ≤ c0) (g1 : 2 ≤ c1) (g2 : 2 ≤ c2) (g3 : 2 ≤ c3)
    (hc : c0 * c1 * c2 * c3 < 2 * ((c0 - 1) * (c1 - 1) * (c2 - 1) * (c3 - 1))) :
    x0 * x1 * x2 * x3 < 2 * ((x0 - 1) * (x1 - 1) * (x2 - 1) * (x3 - 1)) := by
  have k : ∀ x c : ℤ, c ≤ x → 2 ≤ c → x * (c - 1) ≤ c * (x - 1) := fun x c h g => by nlinarith
  have p : ∀ x c : ℤ, c ≤ x → 2 ≤ c → 0 ≤ x * (c - 1) := fun x c h g => by nlinarith
  have A := mul4_le _ _ _ _ _ _ _ _ (k _ _ h0 g0) (k _ _ h1 g1) (k _ _ h2 g2) (k _ _ h3 g3)
    (p _ _ h0 g0) (p _ _ h1 g1) (p _ _ h2 g2) (p _ _ h3 g3)
  have r1 : x0 * (c0 - 1) * (x1 * (c1 - 1)) * (x2 * (c2 - 1)) * (x3 * (c3 - 1)) =
      (x0 * x1 * x2 * x3) * ((c0 - 1) * (c1 - 1) * (c2 - 1) * (c3 - 1)) := by ring
  have r2 : c0 * (x0 - 1) * (c1 * (x1 - 1)) * (c2 * (x2 - 1)) * (c3 * (x3 - 1)) =
      (c0 * c1 * c2 * c3) * ((x0 - 1) * (x1 - 1) * (x2 - 1) * (x3 - 1)) := by ring
  rw [r1, r2] at A
  have hCm : 0 < (c0 - 1) * (c1 - 1) * (c2 - 1) * (c3 - 1) := by
    have := mul4_le 1 1 1 1 (c0 - 1) (c1 - 1) (c2 - 1) (c3 - 1) (by linarith) (by linarith)
      (by linarith) (by linarith) zero_le_one zero_le_one zero_le_one zero_le_one
    linarith
  have hXm : 0 < (x0 - 1) * (x1 - 1) * (x2 - 1) * (x3 - 1) := by
    have := mul4_le 1 1 1 1 (x0 - 1) (x1 - 1) (x2 - 1) (x3 - 1) (by linarith) (by linarith)
      (by linarith) (by linarith) zero_le_one zero_le_one zero_le_one zero_le_one
    linarith
  generalize (c0 - 1) * (c1 - 1) * (c2 - 1) * (c3 - 1) = Cm at A hCm hc
  generalize (x0 - 1) * (x1 - 1) * (x2 - 1) * (x3 - 1) = Xm at A hXm ⊢
  generalize c0 * c1 * c2 * c3 = Cp at A hc
  generalize x0 * x1 * x2 * x3 = Xp at A ⊢
  have B := mul_lt_mul_of_pos_right hc hXm
  have C : Xp * Cm < (2 * Xm) * Cm := by nlinarith
  exact lt_of_mul_lt_mul_right C hCm.le

/-- The prime sets allowed by the abundancy bound. -/
theorem hi_cases (p0 p1 p2 p3 : ℕ) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (h3 : 3 ≤ p0) (h01 : p0 < p1) (h12 : p1 < p2) (h23 : p2 < p3) (o0 : p0 % 2 = 1)
    (o1 : p1 % 2 = 1) (o2 : p2 % 2 = 1) (o3 : p3 % 2 = 1)
    (hZ : 2 * (((p0 : ℤ) - 1) * ((p1 : ℤ) - 1) * ((p2 : ℤ) - 1) * ((p3 : ℤ) - 1)) ≤
      (p0 : ℤ) * p1 * p2 * p3) :
    p0 = 3 ∧ ((p1 = 5 ∧ (p2 = 7 ∨ p2 = 11 ∨ p2 = 13 ∨ (p2 = 17 ∧ p3 ≤ 256) ∨
      (p2 = 19 ∧ p3 ≤ 96) ∨ (p2 = 23 ∧ p3 ≤ 50) ∨ (p2 = 29 ∧ p3 ≤ 34))) ∨
      (p1 = 7 ∧ ((p2 = 11 ∧ p3 ≤ 26) ∨ (p2 = 13 ∧ p3 ≤ 19)))) := by
  have bad : ∀ c0 c1 c2 c3 : ℕ, c0 ≤ p0 → c1 ≤ p1 → c2 ≤ p2 → c3 ≤ p3 → 2 ≤ c0 → 2 ≤ c1 →
      2 ≤ c2 → 2 ≤ c3 → (c0 : ℤ) * c1 * c2 * c3 <
        2 * (((c0 : ℤ) - 1) * ((c1 : ℤ) - 1) * ((c2 : ℤ) - 1) * ((c3 : ℤ) - 1)) → False := by
    intro c0 c1 c2 c3 a0 a1 a2 a3 b0 b1 b2 b3 hc
    exact absurd hZ (not_le.2 (mono4 _ _ _ _ _ _ _ _ (by exact_mod_cast a0) (by exact_mod_cast a1)
      (by exact_mod_cast a2) (by exact_mod_cast a3) (by exact_mod_cast b0) (by exact_mod_cast b1)
      (by exact_mod_cast b2) (by exact_mod_cast b3) hc))
  have np : ∀ n : ℕ, n.Prime → n ≠ 9 ∧ n ≠ 15 ∧ n ≠ 21 ∧ n ≠ 25 ∧ n ≠ 27 := by
    intro n hn
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> rintro rfl <;> norm_num at hn
  rcases (by omega : p0 = 3 ∨ 5 ≤ p0) with rfl | h5
  · refine ⟨rfl, ?_⟩
    obtain ⟨n9, -, -, -, -⟩ := np p1 hp1
    rcases (by omega : p1 = 5 ∨ p1 = 7 ∨ 11 ≤ p1) with rfl | rfl | h11
    · left
      refine ⟨rfl, ?_⟩
      obtain ⟨m9, m15, m21, m25, m27⟩ := np p2 hp2
      rcases (by omega : p2 = 7 ∨ p2 = 11 ∨ p2 = 13 ∨ p2 = 17 ∨ p2 = 19 ∨ p2 = 23 ∨ p2 = 29 ∨
          31 ≤ p2) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | h31
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · rcases (by omega : p3 ≤ 256 ∨ 257 ≤ p3) with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))
        · exact (bad 3 5 17 257 le_rfl le_rfl le_rfl h (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
      · rcases (by omega : p3 ≤ 96 ∨ 97 ≤ p3) with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩))))
        · exact (bad 3 5 19 97 le_rfl le_rfl le_rfl h (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
      · rcases (by omega : p3 ≤ 50 ∨ 51 ≤ p3) with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨rfl, h⟩)))))
        · exact (bad 3 5 23 51 le_rfl le_rfl le_rfl h (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
      · rcases (by omega : p3 ≤ 34 ∨ 35 ≤ p3) with h | h
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨rfl, h⟩)))))
        · exact (bad 3 5 29 35 le_rfl le_rfl le_rfl h (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
      · exact (bad 3 5 31 33 le_rfl le_rfl h31 (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
    · right
      refine ⟨rfl, ?_⟩
      obtain ⟨m9, m15, -, -, -⟩ := np p2 hp2
      rcases (by omega : p2 = 11 ∨ p2 = 13 ∨ 17 ≤ p2) with rfl | rfl | h17
      · rcases (by omega : p3 ≤ 26 ∨ 27 ≤ p3) with h | h
        · exact Or.inl ⟨rfl, h⟩
        · exact (bad 3 7 11 27 le_rfl le_rfl le_rfl h (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
      · rcases (by omega : p3 ≤ 19 ∨ 20 ≤ p3) with h | h
        · exact Or.inr ⟨rfl, h⟩
        · exact (bad 3 7 13 20 le_rfl le_rfl le_rfl h (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num)).elim
      · exact (bad 3 7 17 19 le_rfl le_rfl h17 (by omega) (by norm_num) (by norm_num) (by norm_num)
          (by norm_num) (by norm_num)).elim
    · exact (bad 3 11 13 15 le_rfl h11 (by omega) (by omega) (by norm_num) (by norm_num)
        (by norm_num) (by norm_num) (by norm_num)).elim
  · exact (bad 5 7 9 11 h5 (by omega) (by omega) (by omega) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num)).elim

/-! ### Lower abundancy bounds -/

theorem lo_contra (S0 S1 S2 S3 X0 X1 X2 X3 c0 c1 c2 d0 d1 d2 : ℤ)
    (h0 : c0 * X0 ≤ d0 * S0) (h1 : c1 * X1 ≤ d1 * S1) (h2 : c2 * X2 ≤ d2 * S2) (h3 : X3 ≤ S3)
    (n0 : 0 ≤ X0) (n1 : 0 ≤ X1) (n2 : 0 ≤ X2) (n3 : 0 < X3)
    (k0 : 0 < c0) (k1 : 0 < c1) (k2 : 0 < c2) (k0' : 0 < d0) (k1' : 0 < d1) (k2' : 0 < d2)
    (hK : 0 < X0 * X1 * X2 * X3)
    (hcd : 2 * (d0 * d1 * d2) < c0 * c1 * c2)
    (h : 1 + S0 * S1 * S2 * S3 = 2 * (X0 * X1 * X2 * X3)) : False := by
  have A := mul4_le _ _ _ _ _ _ _ _ h0 h1 h2 h3 (by positivity) (by positivity) (by positivity)
    n3.le
  have r1 : c0 * X0 * (c1 * X1) * (c2 * X2) * X3 = (c0 * c1 * c2) * (X0 * X1 * X2 * X3) := by ring
  have r2 : d0 * S0 * (d1 * S1) * (d2 * S2) * S3 = (d0 * d1 * d2) * (S0 * S1 * S2 * S3) := by ring
  rw [r1, r2] at A
  have hD : 0 < d0 * d1 * d2 := by positivity
  generalize X0 * X1 * X2 * X3 = K at A hK h
  generalize S0 * S1 * S2 * S3 = S at A h
  generalize c0 * c1 * c2 = C at A hcd
  generalize d0 * d1 * d2 = D at A hcd hD
  nlinarith [mul_lt_mul_of_pos_right hcd hK]

/-! ### The largest prime when the first three are `3, 5, q` -/

theorem d_arg (X1 X2 X3 S1 S2 S3 p : ℤ) (hp : 3 ≤ p) (hpodd : p % 2 = 1)
    (e3 : (p - 1) * S3 + 1 = p * X3) (hX3 : p ^ 2 ≤ X3) (hS : 1 ≤ S1 * S2)
    (h : 1 + 13 * S1 * S2 * S3 = 2 * (9 * X1 * X2 * X3)) :
    p * (18 * (X1 * X2) - 13 * (S1 * S2)) < 18 * (X1 * X2) := by
  have key : X3 * (18 * (X1 * X2) - p * (18 * (X1 * X2) - 13 * (S1 * S2))) =
      13 * (S1 * S2) - p + 1 := by
    linear_combination (p - 1) * h - (13 * (S1 * S2)) * e3
  generalize X1 * X2 = Y at key ⊢
  generalize S1 * S2 = Z at key hS ⊢
  rcases lt_trichotomy (18 * Y - p * (18 * Y - 13 * Z)) 0 with ht | ht | ht
  · have : X3 * (18 * Y - p * (18 * Y - 13 * Z)) ≤ -X3 := by nlinarith
    nlinarith
  · rw [ht, mul_zero] at key
    have e : (p - 1) * (18 * Y - p) = 0 := by linear_combination -ht - p * key
    rcases mul_eq_zero.1 e with e | e
    · omega
    · omega
  · linarith

theorem bound11 (X1 X2 S1 S2 p : ℤ) (hp : 3 ≤ p) (e1 : 4 * S1 + 1 = 5 * X1)
    (e2 : 10 * S2 + 1 = 11 * X2) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2)
    (hd : p * (18 * (X1 * X2) - 13 * (S1 * S2)) < 18 * (X1 * X2)) : p < 144 := by
  have A : 4 * S1 * (10 * S2) < 5 * X1 * (11 * X2) :=
    mul_lt_mul'' (by linarith) (by linarith) (by positivity) (by positivity)
  have A' : 40 * (S1 * S2) < 55 * (X1 * X2) := by linarith
  have hZ0 : 0 ≤ S1 * S2 := mul_nonneg hS1 hS2
  generalize X1 * X2 = Y at A' hd
  generalize S1 * S2 = Z at A' hd hZ0
  by_contra hc
  have : (0 : ℤ) ≤ (p - 144) * (18 * Y - 13 * Z) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith

theorem bound13 (X1 X2 S1 S2 p : ℤ) (hp : 3 ≤ p) (e1 : 4 * S1 + 1 = 5 * X1)
    (e2 : 12 * S2 + 1 = 13 * X2) (hS1 : 0 ≤ S1) (hS2 : 0 ≤ S2)
    (hd : p * (18 * (X1 * X2) - 13 * (S1 * S2)) < 18 * (X1 * X2)) : p < 46 := by
  have A : 4 * S1 * (12 * S2) < 5 * X1 * (13 * X2) :=
    mul_lt_mul'' (by linarith) (by linarith) (by positivity) (by positivity)
  have A' : 48 * (S1 * S2) < 65 * (X1 * X2) := by linarith
  have hZ0 : 0 ≤ S1 * S2 := mul_nonneg hS1 hS2
  generalize X1 * X2 = Y at A' hd
  generalize S1 * S2 = Z at A' hd hZ0
  by_contra hc
  have : (0 : ℤ) ≤ (p - 46) * (18 * Y - 13 * Z) :=
    mul_nonneg (by linarith) (by linarith)
  nlinarith


/-! ### The fourth prime, family by family -/

set_option maxHeartbeats 4000000 in
theorem fam17 (p a b c d : ℕ) (hp : p.Prime) (h1 : 17 < p) (h2 : p ≤ 256) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 5, 17, p] [a, b, c, d] = 2 * pP [3, 5, 17, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

set_option maxHeartbeats 4000000 in
theorem fam19 (p a b c d : ℕ) (hp : p.Prime) (h1 : 19 < p) (h2 : p ≤ 96) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 5, 19, p] [a, b, c, d] = 2 * pP [3, 5, 19, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

set_option maxHeartbeats 4000000 in
theorem fam23 (p a b c d : ℕ) (hp : p.Prime) (h1 : 23 < p) (h2 : p ≤ 50) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 5, 23, p] [a, b, c, d] = 2 * pP [3, 5, 23, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

set_option maxHeartbeats 4000000 in
theorem fam29 (p a b c d : ℕ) (hp : p.Prime) (h1 : 29 < p) (h2 : p ≤ 34) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 5, 29, p] [a, b, c, d] = 2 * pP [3, 5, 29, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

set_option maxHeartbeats 4000000 in
theorem fam7_11 (p a b c d : ℕ) (hp : p.Prime) (h1 : 11 < p) (h2 : p ≤ 26) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 7, 11, p] [a, b, c, d] = 2 * pP [3, 7, 11, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

set_option maxHeartbeats 4000000 in
theorem fam7_13 (p a b c d : ℕ) (hp : p.Prime) (h1 : 13 < p) (h2 : p ≤ 19) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 7, 13, p] [a, b, c, d] = 2 * pP [3, 7, 13, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

set_option maxHeartbeats 4000000 in
theorem fam11 (p a b c d : ℕ) (hp : p.Prime) (h1 : 11 < p) (h2 : p < 144) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 5, 11, p] [a, b, c, d] = 2 * pP [3, 5, 11, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

set_option maxHeartbeats 4000000 in
theorem fam13 (p a b c d : ℕ) (hp : p.Prime) (h1 : 13 < p) (h2 : p < 46) (ha : 1 ≤ a)
    (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [3, 5, 13, p] [a, b, c, d] = 2 * pP [3, 5, 13, p] [a, b, c, d]) : False := by
  interval_cases p <;> first
    | (norm_num at hp; done)
    | exact killKey _ (by decide +kernel) a b c d ha hb hc hd h

/-! ### Four sorted primes -/

theorem le_gs (q S X : ℤ) (hq : 3 ≤ q) (e : (q - 1) * S + 1 = q * X) (hX : 1 ≤ X) : X ≤ S := by
  nlinarith

set_option maxHeartbeats 4000000 in
theorem core4 (p0 p1 p2 p3 a b c d : ℕ) (hp0 : p0.Prime) (hp1 : p1.Prime) (hp2 : p2.Prime)
    (hp3 : p3.Prime) (h01 : p0 < p1) (h12 : p1 < p2) (h23 : p2 < p3) (o0 : p0 % 2 = 1)
    (o1 : p1 % 2 = 1) (o2 : p2 % 2 = 1) (o3 : p3 % 2 = 1)
    (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c) (hd : 1 ≤ d)
    (h : 1 + pG [p0, p1, p2, p3] [a, b, c, d] = 2 * pP [p0, p1, p2, p3] [a, b, c, d]) : False := by
  have t3 : ∀ {p : ℕ}, p.Prime → p % 2 = 1 → 3 ≤ p := fun hp ho => by
    have := hp.two_le; omega
  have g0 := t3 hp0 o0
  have g1 := t3 hp1 o1
  have g2 := t3 hp2 o2
  have g3 := t3 hp3 o3
  have hZ : 1 + (gs p0 (2 * a + 1) : ℤ) * gs p1 (2 * b + 1) * gs p2 (2 * c + 1) * gs p3 (2 * d + 1)
      = 2 * ((p0 : ℤ) ^ (2 * a) * (p1 : ℤ) ^ (2 * b) * (p2 : ℤ) ^ (2 * c) * (p3 : ℤ) ^ (2 * d)) := by
    have h' := congrArg (fun n : ℕ => (n : ℤ)) h
    simp only [pG_cons, pG_nil, pP_cons, pP_nil, mul_one] at h'
    push_cast at h'
    linear_combination h'
  obtain ⟨f0, x0⟩ := pfacts g0 ha
  obtain ⟨f1, x1⟩ := pfacts g1 hb
  obtain ⟨f2, x2⟩ := pfacts g2 hc
  obtain ⟨f3, x3⟩ := pfacts g3 hd
  have G0 : (3 : ℤ) ≤ p0 := by exact_mod_cast g0
  have G1 : (3 : ℤ) ≤ p1 := by exact_mod_cast g1
  have G2 : (3 : ℤ) ≤ p2 := by exact_mod_cast g2
  have G3 : (3 : ℤ) ≤ p3 := by exact_mod_cast g3
  have hhi := hi_bound _ _ _ _ _ _ _ _ _ _ _ _ G0 G1 G2 G3 (by nlinarith) (by nlinarith)
    (by nlinarith) (by nlinarith) f0 f1 f2 f3 hZ
  obtain ⟨rfl, hcase⟩ := hi_cases p0 p1 p2 p3 hp1 hp2 g0 h01 h12 h23 o0 o1 o2 o3 hhi
  have S3 := le_gs _ _ _ G3 f3 (by nlinarith)
  have X3p : (0 : ℤ) < (p3 : ℤ) ^ (2 * d) := by positivity
  rcases hcase with ⟨rfl, hcase⟩ | ⟨rfl, hcase⟩
  · rcases hcase with rfl | rfl | rfl | ⟨rfl, hb3⟩ | ⟨rfl, hb3⟩ | ⟨rfl, hb3⟩ | ⟨rfl, hb3⟩
    · -- `3, 5, 7`: too abundant
      simp only [Nat.cast_ofNat] at f0 f1 f2 x0 x1 x2 hZ
      have l0 := lo2 3 _ _ (by norm_num) f0 x0
      have l1 := lo2 5 _ _ (by norm_num) f1 x1
      have l2 := lo2 7 _ _ (by norm_num) f2 x2
      norm_num at l0 l1 l2
      exact lo_contra _ _ _ _ _ _ _ _ 13 31 57 9 25 49 l0 l1 l2 S3 (by positivity) (by positivity)
        (by positivity) X3p (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
        (by norm_num) (by positivity) (by norm_num) hZ
    · -- `3, 5, 11, p`: the exponent of `3` is `2`, and `p < 144`
      have hlt : p3 < 144 := by
        simp only [Nat.cast_ofNat] at f0 f1 f2 x0 x1 x2 hZ
        have ha1 : a = 1 := by
          by_contra hne
          have x0' : (3 : ℤ) ^ 4 ≤ 3 ^ (2 * a) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
          have l0 := lo4 3 _ _ (by norm_num) f0 x0'
          have l1 := lo2 5 _ _ (by norm_num) f1 x1
          have l2 := lo2 11 _ _ (by norm_num) f2 x2
          norm_num at l0 l1 l2
          exact lo_contra _ _ _ _ _ _ _ _ 121 31 133 81 25 121 l0 l1 l2 S3 (by positivity)
            (by positivity) (by positivity) X3p (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by positivity) (by norm_num) hZ
        subst ha1
        have e9 : (3 : ℤ) ^ (2 * 1) = 9 := by norm_num
        have e13 : ((gs 3 (2 * 1 + 1) : ℕ) : ℤ) = 13 := by norm_num [gs]
        rw [e9, e13] at hZ
        have s1 : (1 : ℤ) ≤ gs 5 (2 * b + 1) := by nlinarith
        have s2 : (1 : ℤ) ≤ gs 11 (2 * c + 1) := by nlinarith
        have hd' := d_arg _ _ _ _ _ _ _ G3 (by omega) f3 x3 (one_le_mul_of_one_le_of_one_le s1 s2) hZ
        have := bound11 _ _ _ _ _ G3 (by linarith) (by linarith) (by linarith) (by linarith) hd'
        exact_mod_cast this
      exact fam11 p3 a b c d hp3 h23 hlt ha hb hc hd h
    · -- `3, 5, 13, p`: the exponent of `3` is `2`, and `p < 46`
      have hlt : p3 < 46 := by
        simp only [Nat.cast_ofNat] at f0 f1 f2 x0 x1 x2 hZ
        have ha1 : a = 1 := by
          by_contra hne
          have x0' : (3 : ℤ) ^ 4 ≤ 3 ^ (2 * a) := by
            exact_mod_cast Nat.pow_le_pow_right (by norm_num) (by omega)
          have l0 := lo4 3 _ _ (by norm_num) f0 x0'
          have l1 := lo2 5 _ _ (by norm_num) f1 x1
          have l2 := lo2 13 _ _ (by norm_num) f2 x2
          norm_num at l0 l1 l2
          exact lo_contra _ _ _ _ _ _ _ _ 121 31 183 81 25 169 l0 l1 l2 S3 (by positivity)
            (by positivity) (by positivity) X3p (by norm_num) (by norm_num) (by norm_num)
            (by norm_num) (by norm_num) (by norm_num) (by positivity) (by norm_num) hZ
        subst ha1
        have e9 : (3 : ℤ) ^ (2 * 1) = 9 := by norm_num
        have e13 : ((gs 3 (2 * 1 + 1) : ℕ) : ℤ) = 13 := by norm_num [gs]
        rw [e9, e13] at hZ
        have s1 : (1 : ℤ) ≤ gs 5 (2 * b + 1) := by nlinarith
        have s2 : (1 : ℤ) ≤ gs 13 (2 * c + 1) := by nlinarith
        have hd' := d_arg _ _ _ _ _ _ _ G3 (by omega) f3 x3 (one_le_mul_of_one_le_of_one_le s1 s2) hZ
        have := bound13 _ _ _ _ _ G3 (by linarith) (by linarith) (by linarith) (by linarith) hd'
        exact_mod_cast this
      exact fam13 p3 a b c d hp3 h23 hlt ha hb hc hd h
    · exact fam17 p3 a b c d hp3 h23 hb3 ha hb hc hd h
    · exact fam19 p3 a b c d hp3 h23 hb3 ha hb hc hd h
    · exact fam23 p3 a b c d hp3 h23 hb3 ha hb hc hd h
    · exact fam29 p3 a b c d hp3 h23 hb3 ha hb hc hd h
  · rcases hcase with ⟨rfl, hb3⟩ | ⟨rfl, hb3⟩
    · exact fam7_11 p3 a b c d hp3 h23 hb3 ha hb hc hd h
    · exact fam7_13 p3 a b c d hp3 h23 hb3 ha hb hc hd h

/-! ### From `k` to four sorted primes -/

open ArithmeticFunction
open scoped ArithmeticFunction.sigma

/-- No odd almost perfect square has exactly four distinct prime factors. -/
theorem not_card_four : ∀ k : ℕ, Odd k → IsSquare k → k.primeFactors.card = 4 →
    1 + σ 1 k = 2 * k → False := by
  intro k hk hsq hc h
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  obtain ⟨m, rfl⟩ := hsq
  have hm0 : m ≠ 0 := by rintro rfl; simp at hk0
  have hmm0 : m * m ≠ 0 := mul_ne_zero hm0 hm0
  set s := (m * m).primeFactors with hs
  set f := s.orderEmbOfFin hc with hf
  have hprod : ∀ g : ℕ → ℕ, ∏ p ∈ s, g p = g (f 0) * g (f 1) * g (f 2) * g (f 3) := by
    intro g
    conv_lhs => rw [← s.map_orderEmbOfFin_univ hc, Finset.prod_map]
    rw [Fin.prod_univ_four]
    rfl
  have hfac : ∀ p, (m * m).factorization p = 2 * m.factorization p := by
    intro p; rw [Nat.factorization_mul hm0 hm0]; simp [two_mul]
  have info : ∀ i, (f i).Prime ∧ f i % 2 = 1 ∧ 1 ≤ m.factorization (f i) := by
    intro i
    have hp : f i ∈ s := s.orderEmbOfFin_mem hc i
    have hpp := Nat.prime_of_mem_primeFactors hp
    refine ⟨hpp, Nat.odd_iff.1 (hk.of_dvd_nat (Nat.dvd_of_mem_primeFactors hp)), ?_⟩
    have hp' : f i ∈ m.primeFactors := by
      rw [hs, Nat.primeFactors_mul hm0 hm0, Finset.union_self] at hp; exact hp
    exact hpp.factorization_pos_of_dvd hm0 (Nat.dvd_of_mem_primeFactors hp')
  have hdec : m * m = ∏ p ∈ s, p ^ ((m * m).factorization p) := by
    conv_lhs => rw [← Nat.prod_factorization_pow_eq_self hmm0]
    rw [Finsupp.prod, Nat.support_factorization]
  have hsig : σ 1 (m * m) = ∏ p ∈ s, σ 1 (p ^ ((m * m).factorization p)) := by
    rw [IsMultiplicative.multiplicative_factorization (σ 1) isMultiplicative_sigma hmm0,
      Finsupp.prod, Nat.support_factorization]
  rw [hprod] at hdec hsig
  simp only [hfac] at hdec hsig
  have g : ∀ i, σ 1 (f i ^ (2 * m.factorization (f i))) =
      gs (f i) (2 * m.factorization (f i) + 1) := by
    intro i
    rw [sigma_one_apply_prime_pow (info i).1, gs_eq (info i).1.two_le]
  rw [g, g, g, g] at hsig
  have h2 : 1 + pG [f 0, f 1, f 2, f 3] [m.factorization (f 0), m.factorization (f 1),
      m.factorization (f 2), m.factorization (f 3)] = 2 * pP [f 0, f 1, f 2, f 3]
      [m.factorization (f 0), m.factorization (f 1), m.factorization (f 2),
        m.factorization (f 3)] := by
    have h3 := h
    rw [hsig] at h3
    conv_rhs at h3 => rw [hdec]
    simp only [pG_cons, pG_nil, pP_cons, pP_nil, mul_one]
    linarith [h3]
  exact core4 (f 0) (f 1) (f 2) (f 3) _ _ _ _ (info 0).1 (info 1).1 (info 2).1 (info 3).1
    (f.strictMono (by decide)) (f.strictMono (by decide)) (f.strictMono (by decide))
    (info 0).2.1 (info 1).2.1 (info 2).2.1 (info 3).2.1 (info 0).2.2 (info 1).2.2 (info 2).2.2
    (info 3).2.2 h2

end AAP4

theorem OMA.solution : OMA.R_OeisA215926_conjecture_1_R1_H1_R1.H1 := AAP4.not_card_four
