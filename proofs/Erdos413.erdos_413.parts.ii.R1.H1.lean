import OMAReductions.R_Erdos413_erdos_413_parts_ii_R1

/-! A block Brun sieve for the number of distinct prime factors at negative shifts. -/


/- Finite block sieve with a separate forbidden residue set for each prime.
CRT counting is adapted from the repository's Erdős 16 Romanoff H2 proof.
Block expansion and Bonferroni bounds are adapted from @LordMike's Erdős 675 Brun H1 proof.
The local density and remainder now vary with the prime, so that the set of forbidden
shifts may shrink at larger primes. -/

open scoped Classical
open Finset
noncomputable section
namespace Lau413.Brun

theorem count_periodic_mul (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hper : ∀ n, P n ↔ P (n % m)) (q : ℕ) :
    Nat.count P (m * q) = q * Nat.count P m := by
  induction q with
  | zero => simp
  | succ q ih =>
    have hfun : (fun k => P (m * q + k)) = P := by
      funext k; apply propext
      rw [hper (m * q + k), hper k, Nat.mul_add_mod]
    rw [Nat.mul_succ, Nat.count_add, ih]
    have : Nat.count (fun k => P (m * q + k)) m = Nat.count P m := by
      simp_rw [hfun]
    rw [this]; ring

/-- Counting a periodic set in an initial segment: if `P` is `m`-periodic with `K` solutions
in `[0, m)`, then the number of solutions in `[0, N)` is `N K / m` up to an error of at most `K`. -/
theorem card_filter_range_periodic (P : ℕ → Prop) [DecidablePred P] {m : ℕ} (hm : 0 < m)
    (hper : ∀ n, P n ↔ P (n % m)) (N : ℕ) :
    |(((range N).filter P).card : ℝ) - N * ((range m).filter P).card / m|
      ≤ ((range m).filter P).card := by
  rw [← Nat.count_eq_card_filter_range, ← Nat.count_eq_card_filter_range]
  set K := Nat.count P m
  have hN : N = m * (N / m) + N % m := (Nat.div_add_mod N m).symm
  have hc : Nat.count P N = (N / m) * K + Nat.count P (N % m) := by
    conv_lhs => rw [hN]
    rw [Nat.count_add, count_periodic_mul P hper]
    congr 1
    congr 1
    funext k; apply propext
    rw [hper (m * (N / m) + k), hper k, Nat.mul_add_mod]
  have hle : Nat.count P (N % m) ≤ K := Nat.count_monotone P (Nat.mod_lt N hm).le
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsR : ((N % m : ℕ) : ℝ) < m := by exact_mod_cast Nat.mod_lt N hm
  have hNR : (N : ℝ) = m * ((N / m : ℕ) : ℝ) + ((N % m : ℕ) : ℝ) := by exact_mod_cast hN
  rw [hc, abs_le]
  push_cast
  have hleR : ((Nat.count P (N % m) : ℕ) : ℝ) ≤ K := by exact_mod_cast hle
  have hK0 : (0 : ℝ) ≤ K := by positivity
  have e : (N : ℝ) * K / m = ((N / m : ℕ) : ℝ) * K + ((N % m : ℕ) : ℝ) * K / m := by
    rw [hNR]; field_simp
  have h2 : ((N % m : ℕ) : ℝ) * K / m ≤ K := by
    rw [div_le_iff₀ hmR]; nlinarith
  have h3 : 0 ≤ ((N % m : ℕ) : ℝ) * K / m := by positivity
  rw [e]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (Nat.count P (N % m))]


theorem card_filter_range_mul (F : ℕ → Prop) [DecidablePred F] {p : ℕ} (hp : 0 < p) (m : ℕ) :
    ((range (p * m)).filter F).card
      = ∑ j ∈ range p, ((range m).filter (fun t => F (j + p * t))).card := by
  have : ((range (p * m)).filter F).card
      = ((range p ×ˢ range m).filter (fun x => F (x.1 + p * x.2))).card := by
    refine Finset.card_nbij' (fun r => (r % p, r / p)) (fun x => x.1 + p * x.2) ?_ ?_ ?_ ?_
    · intro r hr
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_product] at hr ⊢
      refine ⟨⟨Nat.mod_lt _ hp, ?_⟩, by rw [Nat.mod_add_div]; exact hr.2⟩
      exact Nat.div_lt_of_lt_mul hr.1
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_product] at hx ⊢
      refine ⟨?_, hx.2⟩
      calc x.1 + p * x.2 < p + p * x.2 := by omega
        _ = p * (x.2 + 1) := by ring
        _ ≤ p * m := Nat.mul_le_mul_left _ hx.1.2
    · intro r _
      simp only [Nat.mod_add_div]
    · intro x hx
      simp only [coe_filter, mem_range, Set.mem_ofPred_eq, mem_product] at hx
      simp only
      refine Prod.ext ?_ ?_
      · simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx.1.1]
      · simp only [Nat.add_mul_div_left _ _ hp, Nat.div_eq_of_lt hx.1.1, zero_add]
  rw [this, card_filter, sum_product]
  refine sum_congr rfl fun j _ => ?_
  rw [card_filter]

theorem card_filter_range_shift (P : ℕ → Prop) [DecidablePred P] {m p : ℕ} (hm : 0 < m) (hpm : Nat.Coprime p m)
    (hper : ∀ n, P n ↔ P (n % m)) (j : ℕ) :
    ((range m).filter (fun t => P (j + p * t))).card = ((range m).filter P).card := by
  set f : ℕ → ℕ := fun t => (j + p * t) % m
  have hinj : Set.InjOn f (range m) := by
    intro t ht t' ht' h
    simp only [coe_range, Set.mem_Iio] at ht ht'
    have h1 : j + p * t ≡ j + p * t' [MOD m] := h
    have h2 := Nat.ModEq.add_left_cancel' j h1
    have h3 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hpm) h2
    have := Nat.mod_eq_of_lt ht; have := Nat.mod_eq_of_lt ht'
    unfold Nat.ModEq at h3; omega
  have himg : (range m).image f = range m := by
    apply eq_of_subset_of_card_le
    · intro u hu
      simp only [mem_image, mem_range] at hu ⊢
      obtain ⟨t, _, rfl⟩ := hu
      exact Nat.mod_lt _ hm
    · rw [card_image_of_injOn hinj]
  have hfilt : (range m).filter (fun t => P (j + p * t)) = (range m).filter (fun t => P (f t)) := by
    refine filter_congr fun t _ => ?_
    simp only [f]; exact hper _
  have himg2 : (range m).filter P = ((range m).filter (fun t => P (f t))).image f := by
    ext u
    simp only [mem_filter, mem_image]
    constructor
    · rintro ⟨hu, hP⟩
      rw [← himg] at hu
      obtain ⟨t, ht, rfl⟩ := mem_image.mp hu
      exact ⟨t, ⟨ht, hP⟩, rfl⟩
    · rintro ⟨t, ⟨ht, hP⟩, rfl⟩
      exact ⟨mem_range.mpr (Nat.mod_lt _ hm), hP⟩
  rw [hfilt, himg2, card_image_of_injOn (hinj.mono (filter_subset _ _))]

/-- Chinese remainder count: if each condition `C p` is `p`-periodic, the number of residues
modulo `Π_{p∈S} p` satisfying all of them is `Π_{p∈S} ω(p)`. -/
theorem card_filter_range_prod (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ((range (∏ p ∈ S, p)).filter (fun r => ∀ p ∈ S, C p r)).card
      = ∏ p ∈ S, ((range p).filter (C p)).card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert p S hpS ih =>
    have hp := hS p (mem_insert_self p S)
    have hS' : ∀ q ∈ S, q.Prime := fun q hq => hS q (mem_insert_of_mem hq)
    have hm : 0 < ∏ q ∈ S, q := prod_pos fun q hq => (hS' q hq).pos
    have hcop : Nat.Coprime p (∏ q ∈ S, q) := Nat.Coprime.prod_right fun q hq =>
      (Nat.coprime_primes hp (hS' q hq)).mpr (fun h => hpS (h ▸ hq))
    rw [prod_insert hpS, prod_insert hpS, card_filter_range_mul (fun r => ∀ q ∈ insert p S, C q r) hp.pos, ← ih hS']
    have hperS : ∀ n, (∀ q ∈ S, C q n) ↔ (∀ q ∈ S, C q (n % ∏ q ∈ S, q)) := by
      intro n
      refine forall₂_congr fun q hq => ?_
      have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
      rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
    have step : ∀ j ∈ range p,
        ((range (∏ q ∈ S, q)).filter (fun t => ∀ q ∈ insert p S, C q (j + p * t))).card
          = if C p j then ((range (∏ q ∈ S, q)).filter (fun r => ∀ q ∈ S, C q r)).card else 0 := by
      intro j hj
      have hj' : ∀ t, C p (j + p * t) ↔ C p j := by
        intro t
        rw [hper p, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (mem_range.mp hj)]
      simp_rw [forall_mem_insert, hj']
      split_ifs with hc
      · simp only [hc, true_and]
        convert card_filter_range_shift (fun n => ∀ q ∈ S, C q n) hm hcop hperS j using 2
      · simp [hc]
    rw [sum_congr rfl step, ← sum_filter, sum_const, smul_eq_mul]

/- Residue counts. -/

/-- The number `ω(p)` of residues `r ∈ [0, p)` that are removed by the local condition `C p`. -/
noncomputable def omega (C : ℕ → ℕ → Prop) (p : ℕ) : ℕ := ((range p).filter (C p)).card


/-- The number of `n < N` meeting every condition `C p`, `p ∈ S`, is `N Π_{p∈S} ω(p)/p` up to an
error of at most `Π_{p∈S} ω(p)`. -/
theorem card_residue_error (C : ℕ → ℕ → Prop) (hper : ∀ p n, C p n ↔ C p (n % p))
    (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (N : ℕ) :
    |(((range N).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
        - N * ∏ p ∈ S, ((omega C p : ℝ) / p)| ≤ ∏ p ∈ S, (omega C p : ℝ) := by
  have hm : 0 < ∏ p ∈ S, p := prod_pos fun p hp => (hS p hp).pos
  have hper' : ∀ n, (∀ p ∈ S, C p n) ↔ (∀ p ∈ S, C p (n % ∏ q ∈ S, q)) := by
    intro n
    refine forall₂_congr fun q hq => ?_
    have := Nat.mod_mod_of_dvd n (dvd_prod_of_mem (fun i : ℕ => i) hq)
    rw [hper q (n % ∏ q ∈ S, q), this, ← hper q n]
  have hcount := card_filter_range_periodic (fun n => ∀ p ∈ S, C p n) hm hper' N
  have hK := card_filter_range_prod C hper S hS
  have hK' : (((range (∏ p ∈ S, p)).filter (fun n => ∀ p ∈ S, C p n)).card : ℝ)
      = ∏ p ∈ S, (omega C p : ℝ) := by
    have e : ∏ i ∈ S, omega C i = ∏ p ∈ S, ((range p).filter (C p)).card := rfl
    rw [← Nat.cast_prod, e, ← hK]
  rw [hK'] at hcount
  convert hcount using 3
  rw [prod_div_distrib]; push_cast; ring

def ind (H : ℕ → ℕ → Prop) (S : Finset ℕ) (k : ℕ) : ℝ :=
  if ∀ p ∈ S, H p k then 1 else 0
def phi (H : ℕ → ℕ → Prop) (P : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ S ∈ P.powerset, c S.card * ind H S k
def dens (g : ℕ → ℝ) (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, c S.card * ∏ p ∈ S, (g p / p)
def mass (g : ℕ → ℝ) (P : Finset ℕ) (c : ℕ → ℝ) : ℝ :=
  ∑ S ∈ P.powerset, |c S.card| * ∏ p ∈ S, g p
def nu (H : ℕ → ℕ → Prop) (P : Finset ℕ) (k : ℕ) := (P.filter (fun p => H p k)).card
def sift (H : ℕ → ℕ → Prop) (W : Finset ℕ) (x : ℕ) :=
  (range x).filter (fun k => ∀ p ∈ W, ¬ H p k)

/-- Coefficients of the inclusion-exclusion sum truncated at order `m`. -/
noncomputable def cU (m : ℕ) (i : ℕ) : ℝ := if i ≤ m then (-1) ^ i else 0

/-- Coefficients of the first omitted term of order `m + 1`. -/
noncomputable def cE (m : ℕ) (i : ℕ) : ℝ := if i = m + 1 then 1 else 0

/-- Elementary symmetric sum of degree `i` of the numbers `t b`, `b ∈ P`. -/
noncomputable def esym (t : ℕ → ℝ) (P : Finset ℕ) (i : ℕ) : ℝ :=
  ∑ S ∈ P.powersetCard i, ∏ b ∈ S, t b


theorem ind_union (H : ℕ → ℕ → Prop) (R S : Finset ℕ) (k : ℕ) :
    ind H (R ∪ S) k = ind H R k * ind H S k := by
  simp only [ind, Finset.forall_mem_union]
  split_ifs <;> simp_all

theorem block_lhs (H : ℕ → ℕ → Prop) (R P : Finset ℕ) (c : ℕ → ℝ) (F : ℕ → ℝ) (x : ℕ) :
    ∑ k ∈ range x, ind H R k * (F k * phi H P c k) =
      ∑ S ∈ P.powerset, c S.card * ∑ k ∈ range x, ind H (R ∪ S) k * F k := by
  have h : ∀ k, ind H R k * (F k * phi H P c k) =
      ∑ S ∈ P.powerset, c S.card * (ind H (R ∪ S) k * F k) := by
    intro k
    simp only [phi, Finset.mul_sum, ind_union]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    ring
  simp only [h, Finset.mul_sum]
  exact Finset.sum_comm

theorem block_rhs (g : ℕ → ℝ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ) (δ X : ℝ) :
    X * (∏ b ∈ R, (g b / (b : ℝ))) * (δ * dens g P c) =
      ∑ S ∈ P.powerset, c S.card * (X * (∏ b ∈ R ∪ S, (g b / (b : ℝ))) * δ) := by
  simp only [dens, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) hRP)]
  ring

theorem block_err (g : ℕ → ℝ) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ) (E : ℝ) :
    ∑ S ∈ P.powerset, |c S.card| * ((∏ p ∈ (R ∪ S), g p) * E) = (∏ p ∈ R, g p) * (E * mass g P c) := by
  simp only [mass, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun S hS => ?_)
  rw [Finset.prod_union (Finset.disjoint_of_subset_right (Finset.mem_powerset.mp hS) hRP)]
  ring

theorem block_step (H : ℕ → ℕ → Prop) (R P : Finset ℕ) (hRP : Disjoint R P) (c : ℕ → ℝ)
    (F : ℕ → ℝ) (δ E : ℝ) (x : ℕ)
    (h : ∀ S, S ⊆ P → |∑ k ∈ range x, ind H (R ∪ S) k * F k
        - x * (∏ b ∈ R ∪ S, ((omega H b : ℝ) / b)) * δ| ≤ (∏ p ∈ (R ∪ S), (omega H p : ℝ)) * E) :
    |∑ k ∈ range x, ind H R k * (F k * phi H P c k)
        - x * (∏ b ∈ R, ((omega H b : ℝ) / b)) * (δ * dens (fun p => (omega H p : ℝ)) P c)| ≤
      (∏ p ∈ R, (omega H p : ℝ)) * (E * mass (fun p => (omega H p : ℝ)) P c) := by
  rw [block_lhs, block_rhs _ _ _ hRP, ← block_err _ _ _ hRP, ← Finset.sum_sub_distrib]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S hS => ?_)
  rw [← mul_sub, abs_mul]
  exact mul_le_mul_of_nonneg_left (h S (Finset.mem_powerset.mp hS)) (abs_nonneg _)

theorem prod_main (H : ℕ → ℕ → Prop) (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) (hper : ∀ p n, H p n ↔ H p (n % p))
    (P : ℕ → Finset ℕ) (hPW : ∀ j, P j ⊆ W) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (c : ℕ → ℕ → ℝ) (x n : ℕ) (R : Finset ℕ) (hR : R ⊆ W) (hRP : ∀ j, j < n → Disjoint R (P j)) :
    |∑ k ∈ range x, ind H R k * ∏ j ∈ range n, phi H (P j) (c j) k
        - x * (∏ b ∈ R, ((omega H b : ℝ) / b)) * ∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (c j)| ≤
      (∏ p ∈ R, (omega H p : ℝ)) * ∏ j ∈ range n, mass (fun p => (omega H p : ℝ)) (P j) (c j) := by
  induction n generalizing R with
  | zero =>
    simp only [Finset.prod_range_zero, mul_one]
    simpa only [ind, ← Finset.natCast_card_filter] using card_residue_error H hper R (fun p hp => hW p (hR hp)) x
  | succ n ih =>
    simp only [Finset.prod_range_succ]
    exact block_step H R (P n) (hRP n (Nat.lt_succ_self n)) (c n)
      (fun k => ∏ j ∈ range n, phi H (P j) (c j) k)
      (∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (c j)) (∏ j ∈ range n, mass (fun p => (omega H p : ℝ)) (P j) (c j)) x
      (fun S hS => ih (R ∪ S) (Finset.union_subset hR (hS.trans (hPW n)))
        (fun j hj => Finset.disjoint_union_left.mpr
          ⟨hRP j (by omega), Finset.disjoint_of_subset_left hS (hdisj n j (by omega))⟩))

theorem sum_prod_phi (H : ℕ → ℕ → Prop) (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) (hper : ∀ p n, H p n ↔ H p (n % p))
    (P : ℕ → Finset ℕ) (hPW : ∀ j, P j ⊆ W) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (c : ℕ → ℕ → ℝ) (x n : ℕ) :
    |∑ k ∈ range x, ∏ j ∈ range n, phi H (P j) (c j) k
        - x * ∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (c j)| ≤
      ∏ j ∈ range n, mass (fun p => (omega H p : ℝ)) (P j) (c j) := by
  have h := prod_main H W hW hper P hPW hdisj c x n ∅ (Finset.empty_subset _)
    (fun j _ => Finset.disjoint_empty_left _)
  simpa [ind] using h


theorem phi_eq_sum (H : ℕ → ℕ → Prop) (P : Finset ℕ) (c : ℕ → ℝ) (k : ℕ) :
    phi H P c k =
      ∑ S ∈ (P.filter (fun b => H b k)).powerset, c S.card := by
  simp only [phi, ind, mul_ite, mul_one, mul_zero]
  rw [← Finset.sum_filter]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.subset_iff]
  constructor
  · rintro ⟨h1, h2⟩ x hx
    exact ⟨h1 hx, h2 x hx⟩
  · intro h
    exact ⟨fun x hx => (h hx).1, fun x hx => (h hx).2⟩

theorem phi_eq_choose (H : ℕ → ℕ → Prop) (P : Finset ℕ) (c : ℕ → ℝ) (k L : ℕ)
    (hL : nu H P k ≤ L) :
    phi H P c k = ∑ i ∈ range (L + 1), c i * ((nu H P k).choose i : ℝ) := by
  have hc : (P.filter (fun b => H b k)).card = nu H P k := rfl
  have hsub : Finset.range (nu H P k + 1) ⊆ Finset.range (L + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [phi_eq_sum, Finset.sum_powerset_apply_card, hc, Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [nsmul_eq_mul, mul_comm]
  · intro i _ hi
    rw [Finset.mem_range, not_lt] at hi
    rw [Nat.choose_eq_zero_of_lt (show nu H P k < i by omega), zero_smul]

theorem phiU_eq (H : ℕ → ℕ → Prop) (P : Finset ℕ) (m k : ℕ) :
    phi H P (cU m) k = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((nu H P k).choose i : ℝ) := by
  have hL : nu H P k ≤ nu H P k + m := Nat.le_add_right _ _
  rw [phi_eq_choose H P (cU m) k (nu H P k + m) hL]
  have hsub : Finset.range (m + 1) ⊆ Finset.range (nu H P k + m + 1) :=
    Finset.range_subset_range.mpr (by omega)
  rw [← Finset.sum_subset hsub]
  · refine Finset.sum_congr rfl (fun i hi => ?_)
    have hi' : i ≤ m := by
      rw [Finset.mem_range] at hi
      omega
    simp only [cU, if_pos hi']
  · intro i _ hi
    have hi' : ¬ i ≤ m := by
      rw [Finset.mem_range, not_lt] at hi
      omega
    simp only [cU, if_neg hi', zero_mul]

theorem phiE_eq (H : ℕ → ℕ → Prop) (P : Finset ℕ) (m k : ℕ) :
    phi H P (cE m) k = ((nu H P k).choose (m + 1) : ℝ) := by
  rw [phi_eq_choose H P (cE m) k (nu H P k + (m + 1)) (Nat.le_add_right _ _)]
  rw [Finset.sum_eq_single (m + 1)]
  · simp [cE]
  · intro i _ hi
    simp [cE, hi]
  · intro h
    exfalso
    apply h
    rw [Finset.mem_range]
    omega

theorem alt_choose_bounds (m n : ℕ) (hm : Even m) :
    (if n = 0 then (1 : ℝ) else 0) ≤ ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * (n.choose i : ℝ) ∧
      ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * (n.choose i : ℝ) ≤
        (if n = 0 then (1 : ℝ) else 0) + (n.choose (m + 1) : ℝ) := by
  rcases n with _ | n
  · have hs : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((0 : ℕ).choose i : ℝ) = 1 := by
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        rw [Nat.choose_eq_zero_of_lt (Nat.pos_of_ne_zero hb)]
        simp
      · intro h
        exact absurd (Finset.mem_range.mpr (Nat.succ_pos m)) h
    rw [hs]
    simp
  · have hs : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * ((n + 1).choose i : ℝ) = (n.choose m : ℝ) := by
      have h2 := congrArg (Int.cast : ℤ → ℝ) (Int.alternating_sum_range_choose_eq_choose (n := n) (m := m))
      push_cast at h2
      simpa [hm.neg_one_pow] using h2
    rw [hs, Nat.choose_succ_succ', if_neg (by omega : ¬ (n + 1 = 0))]
    have h0 : (0 : ℝ) ≤ (n.choose m : ℝ) := Nat.cast_nonneg _
    have h1 : (0 : ℝ) ≤ (n.choose (m + 1) : ℝ) := Nat.cast_nonneg _
    push_cast
    constructor <;> linarith

theorem phiU_bounds (H : ℕ → ℕ → Prop) (P : Finset ℕ) (m k : ℕ) (hm : Even m) :
    (if nu H P k = 0 then (1 : ℝ) else 0) ≤ phi H P (cU m) k ∧
      phi H P (cU m) k ≤ (if nu H P k = 0 then (1 : ℝ) else 0) + phi H P (cE m) k := by
  rw [phiU_eq, phiE_eq]
  exact alt_choose_bounds m _ hm

theorem sum_prod_ite_succ (n : ℕ) (e u : ℕ → ℝ) :
    ∑ j ∈ range (n + 1), ∏ i ∈ range (n + 1), (if i = j then e i else u i) =
      (∑ j ∈ range n, ∏ i ∈ range n, (if i = j then e i else u i)) * u n
        + (∏ i ∈ range n, u i) * e n := by
  have h1 : ∀ j ∈ range n, (∏ i ∈ range (n + 1), (if i = j then e i else u i)) =
      (∏ i ∈ range n, (if i = j then e i else u i)) * u n := by
    intro j hj
    have hj' : j < n := Finset.mem_range.mp hj
    rw [Finset.prod_range_succ, if_neg (show ¬ (n = j) by omega)]
  have h2 : ∏ i ∈ range (n + 1), (if i = n then e i else u i) = (∏ i ∈ range n, u i) * e n := by
    rw [Finset.prod_range_succ, if_pos rfl]
    congr 1
    exact Finset.prod_congr rfl (fun i hi => if_neg (show ¬ (i = n) by
      have := Finset.mem_range.mp hi
      omega))
  rw [Finset.sum_range_succ, Finset.sum_congr rfl h1, ← Finset.sum_mul, h2]

theorem prod_ite_mul (n j : ℕ) (hj : j < n) (e u : ℕ → ℝ) :
    (∏ i ∈ range n, (if i = j then e i else u i)) * u j = e j * ∏ i ∈ range n, u i := by
  have hmem : j ∈ range n := Finset.mem_range.mpr hj
  have h1 : ∏ i ∈ (range n).erase j, (if i = j then e i else u i) =
      ∏ i ∈ (range n).erase j, u i :=
    Finset.prod_congr rfl (fun i hi => if_neg (Finset.ne_of_mem_erase hi))
  rw [← Finset.mul_prod_erase (range n) (fun i => if i = j then e i else u i) hmem,
    ← Finset.mul_prod_erase (range n) u hmem, h1, if_pos rfl]
  ring

theorem hooley (n : ℕ) (t u e : ℕ → ℝ) (h0 : ∀ j, 0 ≤ t j) (h1 : ∀ j, t j ≤ u j)
    (h2 : ∀ j, u j ≤ t j + e j) :
    ∏ j ∈ range n, u j - ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then e i else u i) ≤
      ∏ j ∈ range n, t j := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hu : ∀ j, 0 ≤ u j := fun j => le_trans (h0 j) (h1 j)
    have he : ∀ j, 0 ≤ e j := fun j => by linarith [h0 j, h1 j, h2 j]
    have hU : 0 ≤ ∏ i ∈ range n, u i := Finset.prod_nonneg (fun i _ => hu i)
    have hS : 0 ≤ ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then e i else u i) :=
      Finset.sum_nonneg (fun j _ => Finset.prod_nonneg (fun i _ => by
        split_ifs
        · exact he i
        · exact hu i))
    rw [sum_prod_ite_succ, Finset.prod_range_succ u n, Finset.prod_range_succ t n]
    nlinarith [mul_le_mul_of_nonneg_right ih (h0 n), mul_nonneg hU (sub_nonneg.mpr (h2 n)),
      mul_nonneg hS (sub_nonneg.mpr (h1 n))]

theorem ind_sift (H : ℕ → ℕ → Prop) (W : Finset ℕ) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j) (k : ℕ) :
    (if ∀ b ∈ W, ¬ H b k then (1 : ℝ) else 0) =
      ∏ j ∈ range n, (if nu H (P j) k = 0 then (1 : ℝ) else 0) := by
  have hiff : (∀ b ∈ W, ¬ H b k) ↔ (∀ j ∈ range n, nu H (P j) k = 0) := by
    constructor
    · intro h j hj
      unfold nu
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro b hb hex
      exact h b (hPW j hb) hex
    · intro h b hb hdiv
      obtain ⟨j, hj, hbj⟩ := hcov b hb
      have h0 := h j (Finset.mem_range.mpr hj)
      have hpos : 0 < nu H (P j) k := by
        unfold nu
        apply Finset.card_pos.mpr
        exact ⟨b, Finset.mem_filter.mpr ⟨hbj, hdiv⟩⟩
      omega
  rw [Finset.prod_boole]
  by_cases h : ∀ b ∈ W, ¬ H b k
  · rw [if_pos h, if_pos (hiff.mp h)]
  · rw [if_neg h, if_neg (fun h' => h (hiff.mpr h'))]

theorem sift_pointwise (H : ℕ → ℕ → Prop) (W : Finset ℕ) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j)
    (m : ℕ → ℕ) (hm : ∀ j, Even (m j)) (k : ℕ) :
    ∏ j ∈ range n, phi H (P j) (cU (m j)) k
        - ∑ j ∈ range n, ∏ i ∈ range n,
            phi H (P i) (if i = j then cE (m i) else cU (m i)) k ≤
      (if ∀ b ∈ W, ¬ H b k then (1 : ℝ) else 0) := by
  rw [ind_sift H W P n hPW hcov k]
  have h0 : ∀ j, (0 : ℝ) ≤ (if nu H (P j) k = 0 then (1 : ℝ) else 0) := fun j => by
    split_ifs <;> norm_num
  have h1 : ∀ j, (if nu H (P j) k = 0 then (1 : ℝ) else 0) ≤ phi H (P j) (cU (m j)) k :=
    fun j => (phiU_bounds H (P j) (m j) k (hm j)).1
  have h2 : ∀ j, phi H (P j) (cU (m j)) k ≤
      (if nu H (P j) k = 0 then (1 : ℝ) else 0) + phi H (P j) (cE (m j)) k :=
    fun j => (phiU_bounds H (P j) (m j) k (hm j)).2
  have key : ∏ j ∈ range n, phi H (P j) (cU (m j)) k
      - ∑ j ∈ range n, ∏ i ∈ range n,
          (if i = j then phi H (P i) (cE (m i)) k else phi H (P i) (cU (m i)) k)
      ≤ ∏ j ∈ range n, (if nu H (P j) k = 0 then (1 : ℝ) else 0) :=
    hooley n (fun j => if nu H (P j) k = 0 then (1 : ℝ) else 0)
      (fun j => phi H (P j) (cU (m j)) k) (fun j => phi H (P j) (cE (m j)) k) h0 h1 h2
  have hc : ∑ j ∈ range n, ∏ i ∈ range n, phi H (P i) (if i = j then cE (m i) else cU (m i)) k
      = ∑ j ∈ range n, ∏ i ∈ range n,
          (if i = j then phi H (P i) (cE (m i)) k else phi H (P i) (cU (m i)) k) := by
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.prod_congr rfl
    intro i _
    split_ifs <;> rfl
  rw [hc]
  exact key

theorem sieve_sum (H : ℕ → ℕ → Prop) (W : Finset ℕ) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j)
    (m : ℕ → ℕ) (hm : ∀ j, Even (m j)) (x : ℕ) :
    ∑ k ∈ range x, ∏ j ∈ range n, phi H (P j) (cU (m j)) k
        - ∑ j ∈ range n, ∑ k ∈ range x, ∏ i ∈ range n,
            phi H (P i) (if i = j then cE (m i) else cU (m i)) k ≤
      ((sift H W x).card : ℝ) := by
  unfold sift
  rw [Finset.natCast_card_filter]
  have h : ∑ j ∈ range n, ∑ k ∈ range x, ∏ i ∈ range n, phi H (P i) (if i = j then cE (m i) else cU (m i)) k
      = ∑ k ∈ range x, ∑ j ∈ range n, ∏ i ∈ range n, phi H (P i) (if i = j then cE (m i) else cU (m i)) k :=
    Finset.sum_comm
  rw [h, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro k _
  exact sift_pointwise H W P n hPW hcov m hm k

theorem sieve_lower (H : ℕ → ℕ → Prop) (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime) (hper : ∀ p n, H p n ↔ H p (n % p))
    (P : ℕ → Finset ℕ) (n : ℕ) (hPW : ∀ j, P j ⊆ W)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j)
    (m : ℕ → ℕ) (hm : ∀ j, Even (m j)) (x : ℕ) :
    x * (∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (cU (m j))
          - ∑ j ∈ range n, ∏ i ∈ range n,
              dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i)))
        - (∏ j ∈ range n, mass (fun p => (omega H p : ℝ)) (P j) (cU (m j))
          + ∑ j ∈ range n, ∏ i ∈ range n,
              mass (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i))) ≤
      ((sift H W x).card : ℝ) := by
  have h0 : |∑ k ∈ range x, ∏ j ∈ range n, phi H (P j) (cU (m j)) k
      - x * ∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (cU (m j))| ≤
        ∏ j ∈ range n, mass (fun p => (omega H p : ℝ)) (P j) (cU (m j)) :=
    sum_prod_phi H W hW hper P hPW hdisj (fun j => cU (m j)) x n
  have h1 : ∀ j, |∑ k ∈ range x, ∏ i ∈ range n, phi H (P i) (if i = j then cE (m i) else cU (m i)) k
      - x * ∏ i ∈ range n, dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i))| ≤
        ∏ i ∈ range n, mass (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i)) :=
    fun j => sum_prod_phi H W hW hper P hPW hdisj (fun i => if i = j then cE (m i) else cU (m i)) x n
  have hs := sieve_sum H W P n hPW hcov m hm x
  have hl : x * ∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (cU (m j))
      - ∏ j ∈ range n, mass (fun p => (omega H p : ℝ)) (P j) (cU (m j))
      ≤ ∑ k ∈ range x, ∏ j ∈ range n, phi H (P j) (cU (m j)) k := by
    have := (abs_le.mp h0).1
    linarith
  have hu : ∀ j, ∑ k ∈ range x, ∏ i ∈ range n, phi H (P i) (if i = j then cE (m i) else cU (m i)) k
      ≤ x * ∏ i ∈ range n, dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i))
        + ∏ i ∈ range n, mass (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i)) := by
    intro j
    have := (abs_le.mp (h1 j)).2
    linarith
  have hsumu : ∑ j ∈ range n, ∑ k ∈ range x, ∏ i ∈ range n, phi H (P i) (if i = j then cE (m i) else cU (m i)) k
      ≤ ∑ j ∈ range n, (x * ∏ i ∈ range n, dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i))
        + ∏ i ∈ range n, mass (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i))) :=
    Finset.sum_le_sum (fun j _ => hu j)
  have hsplit : ∑ j ∈ range n, (x * ∏ i ∈ range n, dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i))
        + ∏ i ∈ range n, mass (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i)))
      = x * ∑ j ∈ range n, ∏ i ∈ range n, dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i))
        + ∑ j ∈ range n, ∏ i ∈ range n, mass (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i)) := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
  have hD : x * (∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (cU (m j))
      - ∑ j ∈ range n, ∏ i ∈ range n, dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i)))
      = x * ∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (cU (m j))
        - x * ∑ j ∈ range n, ∏ i ∈ range n, dens (fun p => (omega H p : ℝ)) (P i) (if i = j then cE (m i) else cU (m i)) :=
    mul_sub _ _ _
  linarith

theorem esym_zero (t : ℕ → ℝ) (P : Finset ℕ) : esym t P 0 = 1 := by
  unfold esym
  simp

theorem esym_insert (t : ℕ → ℝ) (P : Finset ℕ) (b : ℕ) (hb : b ∉ P) (i : ℕ) :
    esym t (insert b P) (i + 1) = esym t P (i + 1) + t b * esym t P i := by
  have hdisj : Disjoint (P.powersetCard (i + 1)) ((P.powersetCard i).image (insert b)) := by
    rw [Finset.disjoint_left]
    intro S hS hS'
    obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS'
    exact hb ((Finset.mem_powersetCard.mp hS).1 (Finset.mem_insert_self b T))
  have hinj : Set.InjOn (insert b) ((P.powersetCard i : Finset (Finset ℕ)) : Set (Finset ℕ)) := by
    intro T hT T' hT' h
    have hTb : b ∉ T := fun h' => hb ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT)).1 h')
    have hT'b : b ∉ T' := fun h' => hb ((Finset.mem_powersetCard.mp (Finset.mem_coe.mp hT')).1 h')
    have h1 : (insert b T).erase b = (insert b T').erase b := by rw [h]
    rwa [Finset.erase_insert hTb, Finset.erase_insert hT'b] at h1
  unfold esym
  rw [Finset.powersetCard_succ_insert hb, Finset.sum_union hdisj, Finset.sum_image hinj,
    Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro T hT
  have hTb : b ∉ T := fun h' => hb ((Finset.mem_powersetCard.mp hT).1 h')
  rw [Finset.prod_insert hTb]

theorem esym_nonneg (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b) (i : ℕ) :
    0 ≤ esym t P i := by
  unfold esym
  apply Finset.sum_nonneg
  intro S hS
  apply Finset.prod_nonneg
  intro b hb
  exact ht b ((Finset.mem_powersetCard.mp hS).1 hb)

theorem dens_eq (g : ℕ → ℝ) (P : Finset ℕ) (c : ℕ → ℝ) :
    dens g P c = ∑ i ∈ range (P.card + 1), c i * esym (fun b => g b / (b : ℝ)) P i := by
  unfold dens esym
  have hmaps : ∀ S ∈ P.powerset, S.card ∈ range (P.card + 1) := fun S hS => by
    rw [Finset.mem_range]
    have := Finset.card_le_card (Finset.mem_powerset.mp hS)
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  apply Finset.sum_congr rfl
  intro i _
  rw [← Finset.powersetCard_eq_filter, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S hS
  rw [(Finset.mem_powersetCard.mp hS).2]

theorem dens_cU (g : ℕ → ℝ) (P : Finset ℕ) (m : ℕ) :
    dens g P (cU m) = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym (fun b => g b / (b : ℝ)) P i := by
  have hz : ∀ x, P.card < x → esym (fun b => g b / (b : ℝ)) P x = 0 := by
    intro x hx
    unfold esym
    rw [Finset.powersetCard_eq_empty.mpr hx, Finset.sum_empty]
  rw [dens_eq]
  calc ∑ i ∈ range (P.card + 1), cU m i * esym (fun b => g b / (b : ℝ)) P i
      = ∑ i ∈ range (P.card + m + 2), cU m i * esym (fun b => g b / (b : ℝ)) P i := by
        apply Finset.sum_subset
        · intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        · intro x _ hx
          simp only [Finset.mem_range, not_lt] at hx
          rw [hz x (by omega), mul_zero]
    _ = ∑ i ∈ range (m + 1), cU m i * esym (fun b => g b / (b : ℝ)) P i := by
        symm
        apply Finset.sum_subset
        · intro x hx
          simp only [Finset.mem_range] at hx ⊢
          omega
        · intro x _ hx
          simp only [Finset.mem_range, not_lt] at hx
          simp [cU, show ¬ x ≤ m by omega]
    _ = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym (fun b => g b / (b : ℝ)) P i := by
        apply Finset.sum_congr rfl
        intro x hx
        have hx' : x ≤ m := by
          simp only [Finset.mem_range] at hx
          omega
        simp [cU, hx']

theorem dens_cE (g : ℕ → ℝ) (P : Finset ℕ) (m : ℕ) :
    dens g P (cE m) = esym (fun b => g b / (b : ℝ)) P (m + 1) := by
  rw [dens_eq, Finset.sum_eq_single (m + 1)]
  · simp [cE]
  · intro i _ hi
    simp [cE, hi]
  · intro hn
    have hn' : P.card < m + 1 := by
      simp only [Finset.mem_range, not_lt] at hn
      omega
    unfold esym
    rw [Finset.powersetCard_eq_empty.mpr hn', Finset.sum_empty]
    simp

theorem altsum_insert (t : ℕ → ℝ) (P : Finset ℕ) (b : ℕ) (hb : b ∉ P) (m : ℕ) :
    ∑ i ∈ range (m + 2), (-1 : ℝ) ^ i * esym t (insert b P) i =
      ∑ i ∈ range (m + 2), (-1 : ℝ) ^ i * esym t P i
        - t b * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i := by
  have e1 : ∑ i ∈ range (m + 1), (-1 : ℝ) ^ (i + 1) * esym t (insert b P) (i + 1)
      = ∑ i ∈ range (m + 1), (-1 : ℝ) ^ (i + 1) * esym t P (i + 1)
        - t b * ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [esym_insert t P b hb i]
    ring
  rw [show m + 2 = m + 1 + 1 from rfl]
  rw [Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * esym t (insert b P) i) (m + 1),
    Finset.sum_range_succ' (fun i => (-1 : ℝ) ^ i * esym t P i) (m + 1)]
  rw [e1]
  simp only [esym_zero]
  ring

theorem bonf_aux1 (t : ℕ → ℝ) (i : ℕ) : esym t ∅ (i + 1) = 0 := by
  unfold esym
  rw [Finset.powersetCard_eq_empty.mpr (show (∅ : Finset ℕ).card < i + 1 by simp)]
  simp

theorem bonf_aux2 (t : ℕ → ℝ) (m : ℕ) :
    ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t ∅ i = 1 := by
  rw [Finset.sum_range_succ']
  simp [bonf_aux1, esym_zero]

theorem bonf (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b ∧ t b ≤ 1) (m : ℕ) :
    (Even m → ∏ b ∈ P, (1 - t b) ≤ ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i) ∧
      (Odd m → ∑ i ∈ range (m + 1), (-1 : ℝ) ^ i * esym t P i ≤ ∏ b ∈ P, (1 - t b)) := by
  revert ht m
  refine Finset.induction_on P ?_ ?_
  · intro ht m
    rw [Finset.prod_empty, bonf_aux2]
    exact ⟨fun _ => le_rfl, fun _ => le_rfl⟩
  · intro b P hb ih ht m
    have htb : 0 ≤ t b ∧ t b ≤ 1 := ht b (Finset.mem_insert_self b P)
    have hPt : ∀ c ∈ P, 0 ≤ t c ∧ t c ≤ 1 := fun c hc => ht c (Finset.mem_insert_of_mem hc)
    rw [Finset.prod_insert hb]
    have hP1 : ∏ c ∈ P, (1 - t c) ≤ 1 :=
      Finset.prod_le_one (fun c hc => by linarith [(hPt c hc).2])
        (fun c hc => by linarith [(hPt c hc).1])
    have hP0 : 0 ≤ ∏ c ∈ P, (1 - t c) :=
      Finset.prod_nonneg (fun c hc => by linarith [(hPt c hc).2])
    cases m with
    | zero =>
      simp only [zero_add, Finset.sum_range_one, esym_zero, pow_zero, one_mul]
      refine ⟨fun _ => ?_, fun h => absurd (Nat.odd_iff.mp h) (by norm_num)⟩
      nlinarith [mul_nonneg htb.1 hP0]
    | succ m' =>
      have hA : ∑ i ∈ range (m' + 1 + 1), (-1 : ℝ) ^ i * esym t (insert b P) i =
          ∑ i ∈ range (m' + 1 + 1), (-1 : ℝ) ^ i * esym t P i
            - t b * ∑ i ∈ range (m' + 1), (-1 : ℝ) ^ i * esym t P i :=
        altsum_insert t P b hb m'
      have ihA := ih hPt (m' + 1)
      have ihB := ih hPt m'
      rw [hA]
      rcases Nat.even_or_odd m' with he | ho
      · have hodd : Odd (m' + 1) := he.add_one
        refine ⟨fun h => absurd h (Nat.not_even_iff_odd.mpr hodd), fun _ => ?_⟩
        nlinarith [ihA.2 hodd, ihB.1 he, mul_nonneg htb.1 (sub_nonneg.2 (ihB.1 he))]
      · have hev : Even (m' + 1) := ho.add_one
        refine ⟨fun _ => ?_, fun h => absurd h (Nat.not_odd_iff_even.mpr hev)⟩
        nlinarith [ihA.1 hev, ihB.2 ho, mul_nonneg htb.1 (sub_nonneg.2 (ihB.2 ho))]

theorem pow_succ_add_le (s u : ℝ) (hs : 0 ≤ s) (hu : 0 ≤ u) (i : ℕ) :
    s ^ (i + 1) + (i + 1) * u * s ^ i ≤ (s + u) ^ (i + 1) := by
  induction i with
  | zero => simp
  | succ k ih =>
    push_cast
    have h1 := mul_le_mul_of_nonneg_right ih (add_nonneg hs hu)
    have h2 : 0 ≤ ((k : ℝ) + 1) * u * u * s ^ k := by positivity
    have e1 : (s + u) ^ (k + 1 + 1) = (s + u) ^ (k + 1) * (s + u) := pow_succ _ _
    have e2 : s ^ (k + 1 + 1) = s ^ k * s * s := by ring
    have e3 : s ^ (k + 1) = s ^ k * s := by ring
    rw [e3] at h1
    rw [e1, e2, e3]
    nlinarith [h1, h2]

theorem esym_le (t : ℕ → ℝ) (P : Finset ℕ) (ht : ∀ b ∈ P, 0 ≤ t b) (i : ℕ) :
    esym t P i ≤ (∑ b ∈ P, t b) ^ i / (i.factorial : ℝ) := by
  revert ht i
  refine Finset.induction_on P ?_ ?_
  · intro ht i
    cases i with
    | zero => simp [esym_zero]
    | succ k =>
      rw [bonf_aux1]
      simp
  · intro b P hb ih ht i
    have htb : 0 ≤ t b := ht b (Finset.mem_insert_self b P)
    have hPt : ∀ c ∈ P, 0 ≤ t c := fun c hc => ht c (Finset.mem_insert_of_mem hc)
    have hS : 0 ≤ ∑ c ∈ P, t c := Finset.sum_nonneg hPt
    rw [Finset.sum_insert hb]
    cases i with
    | zero => simp [esym_zero]
    | succ k =>
      rw [esym_insert t P b hb k]
      have ih1 := ih hPt (k + 1)
      have ih0 := ih hPt k
      have key := pow_succ_add_le (∑ c ∈ P, t c) (t b) hS htb k
      have hF : (0 : ℝ) < ((k + 1).factorial : ℝ) := by positivity
      have hk : (0 : ℝ) < (k.factorial : ℝ) := by positivity
      have hfac : ((k + 1).factorial : ℝ) = ((k : ℝ) + 1) * (k.factorial : ℝ) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      have eq1 : (∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ)
          + t b * ((∑ c ∈ P, t c) ^ k / (k.factorial : ℝ))
          = ((∑ c ∈ P, t c) ^ (k + 1) + ((k : ℝ) + 1) * t b * (∑ c ∈ P, t c) ^ k)
              / ((k + 1).factorial : ℝ) := by
        rw [hfac]
        field_simp
      have hle : ((∑ c ∈ P, t c) ^ (k + 1) + ((k : ℝ) + 1) * t b * (∑ c ∈ P, t c) ^ k)
            / ((k + 1).factorial : ℝ)
          ≤ (t b + ∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ) := by
        refine div_le_div_of_nonneg_right ?_ hF.le
        rw [add_comm (t b) (∑ c ∈ P, t c)]
        exact key
      calc esym t P (k + 1) + t b * esym t P k
          ≤ (∑ c ∈ P, t c) ^ (k + 1) / ((k + 1).factorial : ℝ)
              + t b * ((∑ c ∈ P, t c) ^ k / (k.factorial : ℝ)) :=
            add_le_add ih1 (mul_le_mul_of_nonneg_left ih0 htb)
        _ = _ := eq1
        _ ≤ _ := hle

theorem one_sub_ge_exp (G t : ℝ) (hG : 0 ≤ G) (ht : 0 ≤ t) (h : t * (G + 1) ≤ G) :
    Real.exp (-((G + 1) * t)) ≤ 1 - t := by
  have h1 : 0 ≤ 1 - t := by nlinarith
  have h2 := Real.add_one_le_exp ((G + 1) * t)
  have key : 1 ≤ (1 - t) * Real.exp ((G + 1) * t) := by
    nlinarith [mul_le_mul_of_nonneg_left h2 h1, mul_nonneg ht (sub_nonneg.mpr h)]
  rw [Real.exp_neg, inv_eq_one_div, div_le_iff₀ (Real.exp_pos _)]
  linarith

theorem V_ge_exp (G : ℝ) (hG : 0 ≤ G) (t : ℕ → ℝ) (P : Finset ℕ)
    (ht : ∀ b ∈ P, 0 ≤ t b ∧ t b * (G + 1) ≤ G) :
    Real.exp (-((G + 1) * ∑ b ∈ P, t b)) ≤ ∏ b ∈ P, (1 - t b) := by
  have hsum : -((G + 1) * ∑ b ∈ P, t b) = ∑ b ∈ P, -((G + 1) * t b) := by
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  rw [hsum, Real.exp_sum]
  exact Finset.prod_le_prod (fun b _ => Real.exp_nonneg _)
    (fun b hb => one_sub_ge_exp G (t b) hG (ht b hb).1 (ht b hb).2)


theorem main_term (n : ℕ) (sg V ε : ℕ → ℝ) (hV : ∀ j, 0 < V j) (hsg : ∀ j, V j ≤ sg j)
    (hε : ∀ j, 0 ≤ ε j) (hsum : ∑ j ∈ range n, ε j / V j ≤ 1 / 2) :
    1 / 2 * ∏ j ∈ range n, V j ≤
      ∏ j ∈ range n, sg j - ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then ε i else sg i) := by
  have hP0 : 0 ≤ ∏ i ∈ range n, sg i :=
    Finset.prod_nonneg (fun i _ => le_trans (hV i).le (hsg i))
  have hX : ∀ j ∈ range n, (∏ i ∈ range n, (if i = j then ε i else sg i)) ≤
      ε j / V j * ∏ i ∈ range n, sg i := by
    intro j hj
    have hjn : j < n := Finset.mem_range.mp hj
    have hXnn : 0 ≤ ∏ i ∈ range n, (if i = j then ε i else sg i) :=
      Finset.prod_nonneg (fun i _ => by
        split_ifs
        · exact hε i
        · exact le_trans (hV i).le (hsg i))
    have hkey := prod_ite_mul n j hjn ε sg
    have hm : (∏ i ∈ range n, (if i = j then ε i else sg i)) * V j ≤
        (∏ i ∈ range n, (if i = j then ε i else sg i)) * sg j :=
      mul_le_mul_of_nonneg_left (hsg j) hXnn
    rw [div_mul_eq_mul_div, le_div_iff₀ (hV j)]
    linarith
  have hXsum : ∑ j ∈ range n, (∏ i ∈ range n, (if i = j then ε i else sg i)) ≤
      ∑ j ∈ range n, ε j / V j * ∏ i ∈ range n, sg i := Finset.sum_le_sum hX
  rw [← Finset.sum_mul] at hXsum
  have h2 : (∑ j ∈ range n, ε j / V j) * ∏ i ∈ range n, sg i ≤ 1 / 2 * ∏ i ∈ range n, sg i :=
    mul_le_mul_of_nonneg_right hsum hP0
  have hV' : ∏ i ∈ range n, V i ≤ ∏ i ∈ range n, sg i :=
    Finset.prod_le_prod (fun i _ => (hV i).le) (fun i _ => hsg i)
  linarith


/-- The first omitted term relative to the unsieved density is exponentially small when
the degree exceeds a constant times the expected number of hits in the block. -/
theorem relative_remainder (P : Finset ℕ) (g : ℕ → ℝ) (q : ℕ) (a : ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p / p ∧ g p / p ≤ 1 / 2)
    (hq : 4 * (∑ p ∈ P, g p / p) + a ≤ q * Real.log 2) :
    esym (fun p => g p / p) P q ≤ Real.exp (-a) * ∏ p ∈ P, (1 - g p / p) := by
  let μ := ∑ p ∈ P, g p / p
  have hμ : 0 ≤ μ := sum_nonneg (fun p hp => (hg p hp).1)
  have hV : Real.exp (-(2*μ)) ≤ ∏ p ∈ P, (1 - g p / p) := by
    convert V_ge_exp 1 (by norm_num) (fun p => g p / p) P (fun p hp =>
      ⟨(hg p hp).1, by linarith [(hg p hp).2]⟩) using 2
    norm_num [μ]
  have hfact := Real.pow_div_factorial_le_exp (2*μ) (show 0 ≤ 2*μ by positivity) q
  rw [mul_pow, mul_div_assoc] at hfact
  have hpow : ((2:ℝ)^q) = Real.exp (q * Real.log 2) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  have hq' : 2 * μ ≤ -a - 2*μ + q * Real.log 2 := by dsimp [μ]; linarith
  calc
    _ ≤ μ ^ q / (q.factorial : ℝ) := esym_le _ P (fun p hp => (hg p hp).1) q
    _ ≤ Real.exp (-a - 2*μ) := by
      apply le_of_mul_le_mul_left _ (pow_pos (by norm_num : (0:ℝ)<2) q)
      apply hfact.trans
      rw [hpow, ← Real.exp_add]
      exact Real.exp_le_exp.mpr (by linarith)
    _ ≤ _ := by
      rw [sub_eq_add_neg, Real.exp_add]
      exact mul_le_mul_of_nonneg_left hV (Real.exp_pos _).le

theorem density_bounds (P : Finset ℕ) (g : ℕ → ℝ) (m : ℕ) (hm : Even m)
    (hg : ∀ p ∈ P, 0 ≤ g p / p ∧ g p / p ≤ 1) :
    (∏ p ∈ P, (1 - g p / p)) ≤ dens g P (cU m) ∧
      dens g P (cU m) ≤ (∏ p ∈ P, (1 - g p / p)) + dens g P (cE m) := by
  rw [dens_cU, dens_cE]
  constructor
  · exact (bonf _ P hg m).1 hm
  · have h := (bonf _ P hg (m+1)).2 hm.add_one
    rw [sum_range_succ, hm.add_one.neg_one_pow, neg_one_mul] at h
    linarith

/-- Upper sieve with additional required congruences on the primes in R. Blocks can be
shrunk by removing those primes before applying the bound. -/
theorem forced_upper (H : ℕ → ℕ → Prop) (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime)
    (hper : ∀ p n, H p n ↔ H p (n % p)) (P : ℕ → Finset ℕ) (hPW : ∀ j, P j ⊆ W)
    (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j)) (m : ℕ → ℕ) (hm : ∀ j, Even (m j))
    (x n : ℕ) (R : Finset ℕ) (hR : R ⊆ W) (hRP : ∀ j < n, Disjoint R (P j)) :
    (((range x).filter fun k => (∀ p ∈ R, H p k) ∧ ∀ j < n, nu H (P j) k = 0).card : ℝ) ≤
      x * (∏ b ∈ R, ((omega H b : ℝ) / b)) *
        (∏ j ∈ range n, dens (fun p => (omega H p : ℝ)) (P j) (cU (m j))) +
      (∏ p ∈ R, (omega H p : ℝ)) *
        ∏ j ∈ range n, mass (fun p => (omega H p : ℝ)) (P j) (cU (m j)) := by
  let v := fun k j => phi H (P j) (cU (m j)) k
  have hnon : ∀ k j, 0 ≤ v k j := by
    intro k j
    apply le_trans _ (phiU_bounds H (P j) (m j) k (hm j)).1
    split <;> norm_num
  have hmajor : ∀ k, (if (∀ p ∈ R, H p k) ∧ ∀ j < n, nu H (P j) k = 0 then (1:ℝ) else 0) ≤
      ind H R k * ∏ j ∈ range n, v k j := by
    intro k
    split_ifs with hk
    · simp only [ind, if_pos hk.1, one_mul]
      apply one_le_prod
      intro j hj
      simpa [hk.2 j (mem_range.mp hj)] using (phiU_bounds H (P j) (m j) k (hm j)).1
    · apply mul_nonneg _ (prod_nonneg (fun j _ => hnon k j))
      unfold ind
      split <;> norm_num
  have h := (abs_le.mp (prod_main H W hW hper P hPW hdisj (fun j => cU (m j))
    x n R hR hRP)).2
  rw [natCast_card_filter]
  apply (sum_le_sum (fun k _ => hmajor k)).trans
  dsimp only [v]
  linarith only [h]

theorem mass_const_eq (g : ℝ) (P : Finset ℕ) (c : ℕ → ℝ) :
    mass (fun _ => g) P c = ∑ i ∈ range (P.card + 1), (P.card.choose i : ℝ) * (|c i| * g ^ i) := by
  simp only [mass, prod_const]
  rw [Finset.sum_powerset_apply_card (fun i => |c i| * g ^ i)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [nsmul_eq_mul]

theorem choose_sum_le (p m : ℕ) (t : ℝ) (ht : 0 ≤ t) :
    ∑ i ∈ range (m + 2), (p.choose i : ℝ) * t ^ i ≤ (1 + t * p) ^ (m + 1) := by
  rw [add_comm 1, add_pow (t * (p : ℝ)) 1 (m + 1)]
  apply Finset.sum_le_sum
  intro i hi
  have hi' : i ≤ m + 1 := by
    rw [Finset.mem_range] at hi
    omega
  have h1 : (p.choose i : ℝ) ≤ (p : ℝ) ^ i := by exact_mod_cast Nat.choose_le_pow p i
  have h2 : (1 : ℝ) ≤ ((m + 1).choose i : ℝ) := by exact_mod_cast Nat.choose_pos hi'
  have h3 : 0 ≤ t ^ i := pow_nonneg ht i
  have h4 : (p.choose i : ℝ) * t ^ i ≤ (p : ℝ) ^ i * t ^ i := mul_le_mul_of_nonneg_right h1 h3
  have h5 : t ^ i * (p : ℝ) ^ i * 1 ≤ t ^ i * (p : ℝ) ^ i * ((m + 1).choose i : ℝ) :=
    mul_le_mul_of_nonneg_left h2 (mul_nonneg h3 (pow_nonneg (Nat.cast_nonneg p) i))
  rw [one_pow, mul_one, mul_pow]
  nlinarith [h4, h5]

theorem mass_const_le (g : ℝ) (hg : 0 ≤ g) (P : Finset ℕ) (m : ℕ) :
    mass (fun _ => g) P (cU m) + mass (fun _ => g) P (cE m) ≤ (1 + g * P.card) ^ (m + 1) := by
  have hterm : ∀ i, (P.card.choose i : ℝ) * (|cU m i| * g ^ i) + (P.card.choose i : ℝ) * (|cE m i| * g ^ i)
      = if i ≤ m + 1 then (P.card.choose i : ℝ) * g ^ i else 0 := by
    intro i
    unfold cU cE
    by_cases h1 : i ≤ m
    · have h2 : i ≠ m + 1 := by omega
      have h3 : i ≤ m + 1 := by omega
      simp [h1, h2, h3, abs_pow]
    · by_cases h2 : i = m + 1
      · subst h2
        simp
      · have h3 : ¬ i ≤ m + 1 := by omega
        simp [h1, h2, h3]
  rw [mass_const_eq, mass_const_eq, ← Finset.sum_add_distrib]
  calc ∑ i ∈ range (P.card + 1), ((P.card.choose i : ℝ) * (|cU m i| * g ^ i) + (P.card.choose i : ℝ) * (|cE m i| * g ^ i))
      = ∑ i ∈ range (P.card + 1), (if i ≤ m + 1 then (P.card.choose i : ℝ) * g ^ i else 0) :=
        Finset.sum_congr rfl (fun i _ => hterm i)
    _ = ∑ i ∈ (range (P.card + 1)).filter (fun i => i ≤ m + 1), (P.card.choose i : ℝ) * g ^ i :=
        (Finset.sum_filter _ _).symm
    _ ≤ ∑ i ∈ range (m + 2), (P.card.choose i : ℝ) * g ^ i := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
        · intro i hi
          simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
          omega
        · intro i _ _
          exact mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hg _)
    _ ≤ (1 + g * (P.card : ℝ)) ^ (m + 1) := choose_sum_le P.card m g hg

theorem mass_mono (g : ℕ → ℝ) (z : ℝ) (P : Finset ℕ) (c : ℕ → ℝ)
    (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ z) :
    mass g P c ≤ mass (fun _ => z) P c := by
  apply sum_le_sum
  intro S hS
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact prod_le_prod (fun p hp => (hg p ((mem_powerset.mp hS) hp)).1)
    (fun p hp => (hg p ((mem_powerset.mp hS) hp)).2)

theorem mass_bound (P : Finset ℕ) {z : ℕ} (hz : 2 ≤ z) (hP : P.card ≤ z)
    (g : ℕ → ℝ) (hg : ∀ p ∈ P, 0 ≤ g p ∧ g p ≤ z) (m : ℕ) :
    mass g P (cU m) + mass g P (cE m) ≤ (z:ℝ) ^ (3*(m+1)) := by
  have h := (add_le_add (mass_mono g z P (cU m) hg) (mass_mono g z P (cE m) hg)).trans
    (mass_const_le z (by positivity) P m)
  rw [pow_mul]
  apply h.trans
  apply pow_le_pow_left₀ (by positivity)
  have h1 : (2:ℝ) ≤ z := by exact_mod_cast hz
  have h2 : (P.card:ℝ) ≤ z := by exact_mod_cast hP
  nlinarith [mul_nonneg (show (0:ℝ) ≤ z by positivity) (sub_nonneg.mpr h2),
    mul_nonneg (sq_nonneg (z:ℝ)) (sub_nonneg.mpr h1)]

/-- Residue tests for centers start + M n, including both excluded shifts and forced
divisors. A coprime progression preserves the exact number of residues. -/
def hits (res : ℕ → Finset ℕ) (start M p n : ℕ) := (start + M*n) % p ∈ res p

theorem hits_periodic (res : ℕ → Finset ℕ) (start M p n : ℕ) :
    hits res start M p n ↔ hits res start M p (n % p) := by
  simp [hits, Nat.add_mod, Nat.mul_mod]

theorem hits_count (res : ℕ → Finset ℕ) {start M p : ℕ} (hp : 0 < p) (hc : M.Coprime p)
    (hr : res p ⊆ range p) : omega (hits res start M) p = (res p).card := by
  have hper : ∀ n, n % p ∈ res p ↔ n % p % p ∈ res p := by simp
  have h := card_filter_range_shift (fun n => n % p ∈ res p) hp hc hper start
  have he : (range p).filter (fun n => n % p ∈ res p) = res p := by
    ext n
    rw [mem_filter]
    constructor
    · rintro ⟨hn, hrn⟩
      simpa [Nat.mod_eq_of_lt (mem_range.mp hn)] using hrn
    · intro hn
      exact ⟨hr hn, by simpa [Nat.mod_eq_of_lt (mem_range.mp (hr hn))] using hn⟩
  rw [he] at h
  unfold omega
  refine Eq.trans (congrArg card ?_) h
  ext n
  simp only [mem_filter, hits]

/-- Dropping the local tests at the forced primes increases the product density by
at most a factor of two per prime. -/
theorem density_without_forced (W R : Finset ℕ) (t : ℕ → ℝ)
    (ht : ∀ p ∈ W, 0 ≤ t p ∧ t p ≤ 1 / 2) :
    (∏ p ∈ W \ R, (1-t p)) ≤ 2^R.card * ∏ p ∈ W, (1-t p) := by
  let D := W ∩ R
  have hD : D ⊆ W := inter_subset_left
  have he : W \ R = W \ D := by ext p; simp [D]
  have hc : D.card ≤ R.card := card_le_card inter_subset_right
  have hV : ∀ p ∈ W, 0 ≤ 1 - t p := fun p hp => by linarith [(ht p hp).2]
  have hhalf : (1:ℝ) ≤ ∏ p ∈ D, (2*(1-t p)) := by
    apply one_le_prod
    intro p hp
    linarith [(ht p (hD hp)).2]
  rw [prod_mul_distrib, prod_const] at hhalf
  have hVd : 0 ≤ ∏ p ∈ W \ D, (1-t p) := prod_nonneg (fun p hp => hV p (mem_sdiff.mp hp).1)
  rw [he, ← prod_sdiff hD]
  calc
    _ = 1 * (∏ p ∈ W \ D, (1-t p)) := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right hhalf hVd
    _ = 2^D.card * ((∏ p ∈ W \ D, (1-t p)) * ∏ p ∈ D, (1-t p)) := by ring
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hc)
      exact mul_nonneg hVd (prod_nonneg (fun p hp => hV p (hD hp)))

/-- If the local relative errors have small sum, their product costs at most exp(sum). -/
theorem upper_main_term (J : Finset ℕ) (v u e : ℕ → ℝ)
    (hv : ∀ j ∈ J, 0 < v j) (hu : ∀ j ∈ J, 0 ≤ u j)
    (he : ∀ j ∈ J, u j ≤ v j + e j) :
    (∏ j ∈ J, u j) ≤ Real.exp (∑ j ∈ J, e j / v j) * ∏ j ∈ J, v j := by
  rw [Real.exp_sum, ← prod_mul_distrib]
  apply prod_le_prod hu
  intro j hj
  have h := mul_le_mul_of_nonneg_right (Real.add_one_le_exp (e j / v j)) (hv j hj).le
  rw [add_mul, div_mul_cancel₀ _ (hv j hj).ne', one_mul] at h
  linarith [he j hj]

/-- Truncation degree 128·2^h makes the block's relative error summable. -/
theorem block_error (P : Finset ℕ) (g : ℕ → ℝ) (h : ℕ)
    (hg : ∀ p ∈ P, 0 ≤ g p / p ∧ g p / p ≤ 1 / 2)
    (hμ : (∑ p ∈ P, g p / p) ≤ 8*(2:ℝ)^h) :
    dens g P (cE (128 * 2^h)) ≤ (1 / (2:ℝ)^(h+3)) * ∏ p ∈ P, (1-g p / p) := by
  have h2 : (h:ℝ) ≤ (2:ℝ)^h := by exact_mod_cast h.lt_two_pow_self.le
  have h1 : (1:ℝ) ≤ 2^h := one_le_pow₀ (by norm_num)
  have hLog : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hLog' : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
  have hq : 4 * (∑ p ∈ P, g p / p) + (h+3:ℕ) * Real.log 2 ≤
      (128*2^h+1:ℕ) * Real.log 2 := by
    push_cast
    nlinarith [mul_nonneg (show 0 ≤ (2:ℝ)^h by positivity) (sub_nonneg.mpr hLog),
      mul_nonneg (show (0:ℝ) ≤ h by positivity) (sub_nonneg.mpr hLog')]
  have he := relative_remainder P g (128*2^h+1) (((h+3:ℕ):ℝ)*Real.log 2) hg hq
  rw [dens_cE]
  rwa [← Real.log_pow, Real.exp_neg, Real.exp_log (by positivity), inv_eq_one_div] at he

theorem prod_add_ge (n : ℕ) (a b : ℕ → ℝ) (ha : ∀ j, 0 ≤ a j) (hb : ∀ j, 0 ≤ b j) :
    ∏ j ∈ range n, a j + ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then b i else a i) ≤
      ∏ j ∈ range n, (a j + b j) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hS : 0 ≤ ∑ j ∈ range n, ∏ i ∈ range n, (if i = j then b i else a i) := by
      apply Finset.sum_nonneg
      intro j _
      apply Finset.prod_nonneg
      intro i _
      split_ifs
      · exact hb i
      · exact ha i
    rw [sum_prod_ite_succ n b a]
    simp only [Finset.prod_range_succ]
    nlinarith [mul_le_mul_of_nonneg_right ih (add_nonneg (ha n) (hb n)), mul_nonneg hS (hb n)]


/-- Convert the block inequalities into a lower count against the independent local model.
The two budgets bound the aggregate relative truncation error and the CRT counting error. -/
theorem lower_comparison (H : ℕ → ℕ → Prop) (W : Finset ℕ) (hW : ∀ p ∈ W, p.Prime)
    (hper : ∀ p n, H p n ↔ H p (n % p)) (P : ℕ → Finset ℕ) (n : ℕ)
    (hPW : ∀ j, P j ⊆ W) (hdisj : ∀ i j, i ≠ j → Disjoint (P i) (P j))
    (hcov : ∀ b ∈ W, ∃ j, j < n ∧ b ∈ P j) (m : ℕ → ℕ) (hm : ∀ j, Even (m j))
    (x : ℕ) (V : ℕ → ℝ) (hV : ∀ j, 0 < V j)
    (hmodel : ∀ j, V j ≤ dens (fun p => (omega H p:ℝ)) (P j) (cU (m j)))
    (hrel : ∑ j ∈ range n, dens (fun p => (omega H p:ℝ)) (P j) (cE (m j)) / V j ≤ 1/2)
    (herr : (∏ j ∈ range n, (mass (fun p => (omega H p:ℝ)) (P j) (cU (m j)) +
      mass (fun p => (omega H p:ℝ)) (P j) (cE (m j)))) ≤ x * (∏ j ∈ range n, V j) / 4) :
    x * (∏ j ∈ range n, V j) / 4 ≤ ((sift H W x).card : ℝ) := by
  let g := fun p => (omega H p:ℝ)
  have hmass (j) (c) : 0 ≤ mass g (P j) c :=
    sum_nonneg fun _ _ => mul_nonneg (abs_nonneg _) (prod_nonneg (fun _ _ => Nat.cast_nonneg _))
  have hE (j) : 0 ≤ dens g (P j) (cE (m j)) := by
    rw [dens_cE]
    apply esym_nonneg
    exact fun _ _ => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hmain := main_term n (fun j => dens g (P j) (cU (m j))) V
    (fun j => dens g (P j) (cE (m j))) hV hmodel hE hrel
  have hmasses := prod_add_ge n (fun j => mass g (P j) (cU (m j)))
    (fun j => mass g (P j) (cE (m j))) (fun j => hmass j _) (fun j => hmass j _)
  have hlow := sieve_lower H W hW hper P n hPW hdisj hcov m hm x
  have hd (i j : ℕ) : dens g (P i) (if i=j then cE (m i) else cU (m i)) =
      if i=j then dens g (P i) (cE (m i)) else dens g (P i) (cU (m i)) := by split_ifs <;> rfl
  have ha (i j : ℕ) : mass g (P i) (if i=j then cE (m i) else cU (m i)) =
      if i=j then mass g (P i) (cE (m i)) else mass g (P i) (cU (m i)) := by split_ifs <;> rfl
  dsimp only [g] at hd ha hmain hmasses
  simp_rw [hd, ha] at hlow
  linarith only [hlow, hmasses.trans herr, mul_le_mul_of_nonneg_left hmain (Nat.cast_nonneg (α := ℝ) x)]

end Lau413.Brun
end

section

/- Prime reciprocal sums on the large-prime interval. The Abel summation and Chebyshev
lemmas through prime_reciprocal_interval_bounds are from the local Erdős 442 H1 proof,
credited there to @dk8827. -/

open Filter MeasureTheory Asymptotics
open scoped BigOperators Topology
namespace Lau413.Reciprocals

lemma abel_reciprocal (c : ℕ → ℝ) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) volume a b ∧
    ∑ n ∈ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊, c n / (n : ℝ) =
      (∑ n ∈ Finset.Icc 0 ⌊b⌋₊, c n) / b - (∑ n ∈ Finset.Icc 0 ⌊a⌋₊, c n) / a +
        ∫ t in a..b, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2 := by
  let f (t : ℝ) := t⁻¹
  have hne (t : ℝ) (ht : t ∈ Set.Icc a b) : t ≠ 0 := (ha.trans_le ht.1).ne'
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) : HasDerivAt f (-(t ^ 2)⁻¹) t :=
    hasDerivAt_inv (hne t ht)
  have hc : ContinuousOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := by
    have h : ContinuousOn (fun t : ℝ => t ^ 2) (Set.Icc a b) := by fun_prop
    exact h.inv₀ (fun t ht => pow_ne_zero _ (hne t ht))
  have hg : IntegrableOn (fun t : ℝ => (t ^ 2)⁻¹) (Set.Icc a b) := hc.integrableOn_Icc
  have hfd : IntegrableOn (deriv f) (Set.Icc a b) :=
    (hc.neg.congr (fun t ht => (hd t ht).deriv)).integrableOn_Icc
  have hi : IntervalIntegrable (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) volume a b := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab]
    have he : (fun t : ℝ => (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) =
        fun t : ℝ => (t ^ 2)⁻¹ * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) := by
      funext t
      rw [div_eq_mul_inv, mul_comm]
    rw [he]
    exact integrableOn_mul_sum_Icc c ha.le hg
  refine ⟨hi, ?_⟩
  have hf := sum_mul_eq_sub_sub_integral_mul c (f := f) ha.le hab
    (fun t ht => (hd t ht).differentiableAt) hfd
  rw [← intervalIntegral.integral_of_le hab] at hf
  have hint :
      (∫ t in a..b, deriv f t * ∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) =
        -(∫ t in a..b, (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    change deriv f t * (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) = -((∑ n ∈ Finset.Icc 0 ⌊t⌋₊, c n) / t ^ 2)
    rw [(hd t ht).deriv, neg_mul, div_eq_mul_inv, mul_comm ((t ^ 2)⁻¹)]
  rw [hint] at hf
  simpa only [f, div_eq_mul_inv, mul_comm, sub_neg_eq_add] using hf

lemma prime_reciprocal_abel {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2) volume a b ∧
    ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p =
      (Nat.primeCounting ⌊b⌋₊ : ℝ) / b - (Nat.primeCounting ⌊a⌋₊ : ℝ) / a +
        ∫ t in a..b, (Nat.primeCounting ⌊t⌋₊ : ℝ) / t ^ 2 := by
  classical
  let c (n : ℕ) : ℝ := if n.Prime then 1 else 0
  have hc (N : ℕ) : (∑ p ∈ Finset.Icc 0 N, c p) = (Nat.primeCounting N : ℝ) := by
    rw [← Nat.primesLE_card_eq_primeCounting]
    simp only [c, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one,
      ← Nat.range_succ_eq_Icc_zero, Nat.primesLE, Nat.primesBelow]
  obtain ⟨hint, heq⟩ := abel_reciprocal c ha hab
  refine ⟨?_, ?_⟩
  · simpa only [hc] using hint
  simp only [hc] at heq
  rw [← heq, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro p hp
  by_cases h : p.Prime <;> simp [h, c]

theorem prime_reciprocal_interval_bounds :
    ∃ y : ℝ, 1 < y ∧ ∀ a b : ℝ, y ≤ a → a ≤ b →
      let w := ∑ p ∈ (Finset.Ioc ⌊a⌋₊ ⌊b⌋₊).filter Nat.Prime, (1 : ℝ) / p
      let z := Real.log (Real.log b) - Real.log (Real.log a)
      w ≤ (Real.log 4 + 1) * z + (Real.log 4 + 1) / Real.log a := by
  obtain ⟨u, hu⟩ := eventually_atTop.mp
    (Chebyshev.eventually_primeCounting_le (show (0 : ℝ) < 1 by norm_num))
  let y := max u 2
  have hy : 1 < y := (by norm_num : (1:ℝ)<2).trans_le (le_max_right _ _)
  have hY (t : ℝ) (ht : y ≤ t) := hu t ((le_max_left _ _).trans ht)
  refine ⟨y, hy, ?_⟩
  intro a b ha hab
  have ha1 : 1 < a := hy.trans_le ha
  have hb1 : 1 < b := ha1.trans_le hab
  have ha0 : 0 < a := zero_lt_one.trans ha1
  have hb0 : 0 < b := ha0.trans_le hab
  let C := Real.log 4 + 1
  have hC0 : 0 < C := by dsimp [C]; linarith [Real.log_pos (show (1 : ℝ) < 4 by norm_num)]
  let T (t : ℝ) := (Nat.primeCounting ⌊t⌋₊ : ℝ)
  let g (t : ℝ) := t⁻¹ / Real.log t
  obtain ⟨hi, heq⟩ := prime_reciprocal_abel ha0 hab
  have h1 (t : ℝ) (ht : t ∈ Set.Icc a b) : 1 < t := ha1.trans_le ht.1
  have hg : ContinuousOn g (Set.Icc a b) := by
    apply ContinuousOn.div
    · exact continuousOn_id.inv₀ (fun t ht => (zero_lt_one.trans (h1 t ht)).ne')
    · apply Real.continuousOn_log.mono
      intro t ht
      exact Set.mem_compl_singleton_iff.mpr (zero_lt_one.trans (h1 t ht)).ne'
    · exact fun t ht => (Real.log_pos (h1 t ht)).ne'
  have hgi : IntervalIntegrable g volume a b := by
    apply hg.intervalIntegrable_of_Icc hab
  have hfac (d t : ℝ) (ht : 1 < t) : d * g t = (d * t / Real.log t) / t ^ 2 := by
    have ht0 : 0 < t := zero_lt_one.trans ht
    have hlog := Real.log_pos ht
    dsimp [g]
    field_simp
  have hIntU : (∫ t in a..b, T t / t ^ 2) ≤ C * ∫ t in a..b, g t := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_mono_on hab hi (hgi.const_mul C)
    intro t ht
    rw [hfac C t (h1 t ht)]
    exact div_le_div_of_nonneg_right (hY t (ha.trans ht.1)) (sq_nonneg _)
  have hgi_eq : (∫ t in a..b, g t) = Real.log (Real.log b) - Real.log (Real.log a) :=
    integral_inv_div_log ha1 hb1
  rw [hgi_eq] at hIntU
  have hTB : T b / b ≤ C / Real.log a := by
    calc
      _ ≤ C / Real.log b := by
        apply (div_le_iff₀ hb0).mpr
        rw [div_mul_eq_mul_div]
        exact (hY b (ha.trans hab))
      _ ≤ _ := div_le_div_of_nonneg_left hC0.le (Real.log_pos ha1) (Real.log_le_log ha0 hab)
  have hTA0 : 0 ≤ T a / a := by dsimp [T]; positivity
  rw [heq]
  change _ ≤ C * (Real.log (Real.log b) - Real.log (Real.log a)) + C / Real.log a
  linarith only [hIntU, hTB, hTA0]

/-- A polynomial bound on the ratio of endpoint logarithms costs only a logarithm in k. -/
theorem large_prime_sum (A : ℕ) : ∃ y L : ℝ, 2 ≤ y ∧ 0 < L ∧
    ∀ {k : ℕ} {r t : ℝ}, 2 ≤ k → y ≤ r → Real.log t ≤ (k:ℝ)^A * Real.log r →
      (∑ p ∈ (Finset.Ioc ⌊r⌋₊ ⌊t⌋₊).filter Nat.Prime, (1:ℝ) / p) ≤ L * Real.log k := by
  obtain ⟨y, hy, h⟩ := prime_reciprocal_interval_bounds
  let C := Real.log 4 + 1
  have hC : 0 < C := by dsimp [C]; linarith [Real.log_pos (by norm_num : (1:ℝ)<4)]
  refine ⟨max y 2, C * (A + 4), le_max_right _ _, by positivity, ?_⟩
  intro k r t hk hr hratio
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hrR : (2:ℝ) ≤ r := (le_max_right _ _).trans hr
  have hlogr : 1/2 ≤ Real.log r := by linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hrR]
  have hlogk : 1/2 ≤ Real.log k := by linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hkR]
  by_cases hrt : r ≤ t
  · have ht : 1 < t := by linarith
    have hlogs := Real.log_le_log (Real.log_pos ht) hratio
    rw [Real.log_mul (by positivity) (by linarith), Real.log_pow] at hlogs
    have hb := h r t ((le_max_left _ _).trans hr) hrt
    have he : C / Real.log r ≤ 2 * C := by
      apply (div_le_iff₀ (by linarith)).2
      nlinarith [mul_nonneg hC.le (sub_nonneg.mpr hlogr)]
    change _ ≤ C * _ + C / Real.log r at hb
    apply hb.trans
    nlinarith [mul_le_mul_of_nonneg_left (show Real.log (Real.log t) - Real.log (Real.log r) ≤
      A * Real.log k by linarith) hC.le, mul_nonneg hC.le (sub_nonneg.mpr hlogk)]
  · have hempty : Finset.Ioc ⌊r⌋₊ ⌊t⌋₊ = ∅ := Finset.Ioc_eq_empty_of_le (Nat.floor_le_floor (le_of_not_ge hrt))
    simp only [hempty, Finset.filter_empty, Finset.sum_empty]
    positivity

/-- An absolute reciprocal-mass budget for one fourth-power block. -/
theorem fourth_power_block : ∃ y : ℝ, 2 ≤ y ∧ ∀ r ≥ y,
    (∑ p ∈ (Finset.Ioc ⌊r⌋₊ ⌊r^4⌋₊).filter Nat.Prime, (1:ℝ)/p) ≤ 8 := by
  obtain ⟨y, hy, h⟩ := prime_reciprocal_interval_bounds
  refine ⟨max y 2, le_max_right _ _, ?_⟩
  intro r hr
  have hr2 := (le_max_right y 2).trans hr
  have hrlog : 2/3 ≤ Real.log r := by
    linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hr2]
  have hr4 : r ≤ r^4 := by
    calc
      _ = r^1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  have hb := h r (r^4) ((le_max_left _ _).trans hr) hr4
  have hlog4 : Real.log 4 ≤ 7/5 := by
    have he : (4:ℝ) = 2^2 := by norm_num
    rw [he, Real.log_pow]
    linarith [Real.log_two_lt_d9]
  have hlog4pos : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  rw [Real.log_pow, Real.log_mul (by norm_num) (by linarith)] at hb
  have hd : (Real.log 4 + 1) / Real.log r ≤ 4 := by
    apply (div_le_iff₀ (by linarith)).2
    linarith
  apply hb.trans
  norm_num
  nlinarith [mul_nonneg (sub_nonneg.mpr hlog4) (show 0 ≤ Real.log 4 + 1 by linarith)]

end Lau413.Reciprocals
end

section

open Finset
namespace Lau413.Scales

def w (H : ℕ) := 2 ^ (H + 3)
def level (H h : ℕ) := w H ^ (4 ^ (H - h))
def index (k : ℕ) := Nat.log 2 k + 1

theorem w_two_le (H : ℕ) : 2 ≤ w H := by
  apply le_trans (b := 2 ^ 1) (by decide)
  exact Nat.pow_le_pow_right (by decide) (by omega)

theorem level_last (H : ℕ) : level H H = w H := by simp [level]
theorem level_ge (H h : ℕ) : w H ≤ level H h := by
  simpa [level] using Nat.pow_le_pow_right (by have := w_two_le H; omega : 0 < w H)
    (show 0 < 4 ^ (H-h) by positivity)
theorem level_step {H h : ℕ} (hh : h < H) : level H h = level H (h+1) ^ 4 := by
  have he : H-h = (H-(h+1))+1 := by omega
  unfold level
  rw [he, pow_succ 4, pow_mul]

theorem level_antitone (H : ℕ) : Antitone (level H) := by
  intro i j hij
  exact Nat.pow_le_pow_right (by have := w_two_le H; omega)
    (Nat.pow_le_pow_right (by decide) (Nat.sub_le_sub_left hij H))

/-- For every medium prime there is a block that forbids its shift. -/
theorem medium_covered {k p H : ℕ} (hp : w H < p) (hu : p ≤ level H (index k)) :
    ∃ h < H, level H (h+1) < p ∧ p ≤ level H h ∧ k ≤ 2^h := by
  have hlast : ¬p ≤ level H H := by rw [level_last]; omega
  have hi : index k < H := by
    by_contra! hc
    exact hlast (hu.trans (level_antitone H hc))
  let h := Nat.findGreatest (fun h => p ≤ level H h) H
  have hit : p ≤ level H h := Nat.findGreatest_spec (P := fun h => p ≤ level H h) hi.le hu
  have him : index k ≤ h := Nat.le_findGreatest hi.le hu
  have hh : h < H := lt_of_le_of_ne (Nat.findGreatest_le _) (fun he => hlast (he ▸ hit))
  refine ⟨h, hh, ?_, hit, (Nat.lt_pow_succ_log_self (by decide : 1 < 2) k).le.trans
    (Nat.pow_le_pow_right (by decide) him)⟩
  by_contra! he
  have := Nat.le_findGreatest (P := fun a => p ≤ level H a) (Nat.succ_le_of_lt hh) he
  change h+1 ≤ h at this
  omega

/-- The log of the top divided by the log at the shift cutoff grows at most quadratically. -/
theorem log_level_ratio {H k : ℕ} (hk : 0 < k) :
    Real.log (level H 0) ≤ (4 * (k:ℝ)^2) * Real.log (level H (index k)) := by
  have hn := Nat.pow_log_le_self 2 hk.ne'
  have hpow : 4 ^ index k ≤ 4 * k^2 := calc
    _ = 4 * (2 ^ Nat.log 2 k)^2 := by
      rw [index, pow_succ, mul_comm _ 4, ← pow_mul, Nat.mul_comm (Nat.log 2 k) 2, pow_mul]
      rfl
    _ ≤ _ := by gcongr
  have hsum : H ≤ index k + (H-index k) := by omega
  have h : 4^H ≤ (4*k^2)*4^(H-index k) := calc
    _ ≤ 4^(index k + (H-index k)) := Nat.pow_le_pow_right (by decide) hsum
    _ ≤ _ := by rw [pow_add]; exact Nat.mul_le_mul_right _ hpow
  have h' : (4:ℝ)^H ≤ (4 * (k:ℝ)^2) * 4^(H-index k) := by exact_mod_cast h
  have hw : 0 ≤ Real.log (w H) := Real.log_nonneg (by exact_mod_cast (w_two_le H).trans' (by decide : 1 ≤ 2))
  simpa [level, Real.log_pow, mul_assoc] using mul_le_mul_of_nonneg_right h' hw

theorem geometric_cost (H : ℕ) :
    ∑ h ∈ range H, 2^h * 4^(H-h) + 2 * 2^H = 2*4^H := by
  induction H with
  | zero => simp
  | succ H ih =>
    rw [sum_range_succ]
    have hf : ∀ h ∈ range H, 2^h * 4^(H+1-h) = 4*(2^h * 4^(H-h)) := by
      intro h hh
      have : H+1-h = H-h+1 := by have := mem_range.mp hh; omega
      rw [this, pow_succ]; ring
    rw [sum_congr rfl hf, ← mul_sum]
    simp only [Nat.add_sub_cancel_left, pow_succ, pow_zero, one_mul]
    omega

/-- The total degree cost fits in a fixed power of the largest level. -/
theorem degree_cost (H d : ℕ) :
    ∑ h ∈ range H, (d * 2^h) * 4^(H-h) ≤ 2 * d * 4^H := by
  simp_rw [mul_assoc d, ← mul_sum]
  have h := geometric_cost H
  calc
    _ ≤ d * (2 * 4^H) := Nat.mul_le_mul_left d (by omega)
    _ = _ := by ring

/-- In the geometric construction the endpoint logarithms meet the hypothesis of the
large-prime reciprocal estimate, uniformly over shifts. -/
theorem large_interval_ratio (H D : ℕ) {k b : ℕ} (hk : 2 ≤ k) (hb : 2 ≤ b) :
    Real.log ((level H 0:ℝ)^D) / (b * Real.log k) ≤
      (k:ℝ)^(D+4) * Real.log (level H (index k)) := by
  have hkR : (2:ℝ) ≤ k := by exact_mod_cast hk
  have hbR : (2:ℝ) ≤ b := by exact_mod_cast hb
  have hklog : 1/2 ≤ Real.log k := by
    linarith [Real.log_two_gt_d9, Real.log_le_log (by norm_num) hkR]
  have hden : (1:ℝ) ≤ b * Real.log k := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hbR) (sub_nonneg.mpr hklog)]
  have hbase (j : ℕ) : 0 ≤ Real.log (level H j) := by
    apply Real.log_nonneg
    exact_mod_cast (show 1 ≤ level H j from (w_two_le H).trans' (by decide : 1 ≤ 2) |>.trans (level_ge H j))
  have hd : D ≤ k^D := (Nat.le_of_lt (Nat.lt_two_pow_self (n := D))).trans
    (Nat.pow_le_pow_left hk D)
  have h4 : 4 ≤ k^2 := by nlinarith
  have hcoeff : D * (4*k^2) ≤ k^(D+4) := calc
    _ ≤ k^D * (k^2 * k^2) := Nat.mul_le_mul hd (Nat.mul_le_mul_right _ h4)
    _ = _ := by rw [pow_add]; ring
  rw [Real.log_pow]
  apply (div_le_self (mul_nonneg (Nat.cast_nonneg D) (hbase 0)) hden).trans
  have hr := mul_le_mul_of_nonneg_left (log_level_ratio (H := H) (k := k) (by omega)) (Nat.cast_nonneg (α := ℝ) D)
  rw [← mul_assoc] at hr
  exact hr.trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hcoeff) (hbase _))

def primorial (H : ℕ) := ∏ p ∈ Nat.primesLE (w H), p

theorem prime_dvd_primorial {p H : ℕ} (hp : p.Prime) (h : p ≤ w H) : p ∣ primorial H :=
  dvd_prod_of_mem id (Nat.mem_primesLE.mpr ⟨h, hp⟩)

theorem primorial_le_top {H : ℕ} (hH : 3 ≤ H) : primorial H ≤ level H 0 := by
  have hcard : (Nat.primesLE (w H)).card ≤ w H := by
    have hs : Nat.primesLE (w H) ⊆ Icc 1 (w H) := fun p hp =>
      mem_Icc.mpr ⟨(Nat.mem_primesLE.mp hp).2.one_le, (Nat.mem_primesLE.mp hp).1⟩
    simpa using card_le_card hs
  have hex : w H ≤ 4^H := calc
    _ ≤ 2^(H+H) := Nat.pow_le_pow_right (by decide) (Nat.add_le_add_left hH H)
    _ = 4^H := by rw [← two_mul, pow_mul]; rfl
  calc
    _ ≤ ∏ _p ∈ Nat.primesLE (w H), w H := prod_le_prod' fun p hp => (Nat.mem_primesLE.mp hp).1
    _ ≤ level H 0 := by
      simp only [prod_const, level, Nat.sub_zero]
      exact Nat.pow_le_pow_right (by have := w_two_le H; omega) (hcard.trans hex)

end Lau413.Scales
end


/- Deterministic prime counts and a factorial-moment reduction for negative shifts. -/

noncomputable section

open Finset ArithmeticFunction
open scoped omega Classical

namespace Lau413

theorem omega_eq (m : ℕ) : ω m = m.primeFactors.card := by
  rw [cardDistinctFactors_apply, ← Nat.toFinset_factors, List.card_toFinset]

/-- A subset of the prime divisors above a real threshold has bounded cardinality. -/
theorem log_count {m : ℕ} (hm : 0 < m) {P : Finset ℕ} (hP : P ⊆ m.primeFactors)
    {t : ℝ} (ht : 0 < t) (hp : ∀ p ∈ P, t ≤ p) :
    (P.card : ℝ) * Real.log t ≤ Real.log m := by
  have hd := (Finset.prod_dvd_prod_of_subset P m.primeFactors id hP).trans
    (Nat.prod_primeFactors_dvd m)
  have hprod : t ^ P.card ≤ (m : ℝ) := calc
    t ^ P.card = ∏ _p ∈ P, t := by simp
    _ ≤ ∏ p ∈ P, (p : ℝ) := Finset.prod_le_prod (fun _ _ => ht.le) hp
    _ ≤ m := by
      rw [← Nat.cast_prod]
      exact_mod_cast Nat.le_of_dvd hm hd
  simpa only [Real.log_pow] using Real.log_le_log (pow_pos ht _) hprod

theorem omega_log {m : ℕ} (hm : 0 < m) : (ω m : ℝ) ≤ 2 * Real.log m := by
  have h := log_count hm (Finset.Subset.refl _) (by norm_num : (0 : ℝ) < 2)
    (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).two_le)
  rw [omega_eq]
  nlinarith [Real.log_two_gt_d9, (show (0 : ℝ) ≤ m.primeFactors.card by positivity),
    mul_nonneg (show (0 : ℝ) ≤ m.primeFactors.card by positivity)
      (show 0 ≤ Real.log 2 - 1 / 2 by linarith [Real.log_two_gt_d9])]

def primeBand (m : ℕ) (lo hi : ℝ) : Finset ℕ :=
  m.primeFactors.filter fun p : ℕ => lo < p ∧ (p : ℝ) ≤ hi

theorem small_count {n k : ℕ} (hk : 0 < k) (hkn : k < n) {w : ℝ}
    (hw : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → p ∣ n) :
    (((n-k).primeFactors.filter fun p : ℕ => (p : ℝ) ≤ w).card : ℝ) ≤ 2 * Real.log k := by
  apply le_trans _ (omega_log hk)
  rw [omega_eq, Nat.cast_le]
  apply Finset.card_le_card
  intro p hp
  obtain ⟨hpf, hpw⟩ := Finset.mem_filter.mp hp
  obtain ⟨hpp, hpd, _⟩ := Nat.mem_primeFactors.mp hpf
  exact Nat.mem_primeFactors.mpr ⟨hpp, by
    have h := Nat.dvd_sub (hw p hpp hpw) hpd
    simpa [Nat.sub_sub_self hkn.le] using h, hk.ne'⟩

theorem log_four_ranges {n k : ℕ} (hk : 2 ≤ k) (hkn : k < n) {w r t b a : ℝ}
    (hw : ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → p ∣ n)
    (ht : 1 < t) (htail : Real.log n ≤ b * Real.log k * Real.log t)
    (hmed : ((primeBand (n-k) w r).card : ℝ) ≤ a * Real.log k)
    (hlg : ((primeBand (n-k) r t).card : ℝ) ≤ a * Real.log k) :
    (ω (n-k) : ℝ) ≤ (2 + 2*a + b) * Real.log k := by
  classical
  let F := (n-k).primeFactors
  let U := F.filter fun p : ℕ => (p : ℝ) ≤ w
  let V := primeBand (n-k) w r
  let Z := primeBand (n-k) r t
  let Y := F.filter fun p : ℕ => t < (p : ℝ)
  have hcover : F ⊆ U ∪ V ∪ Z ∪ Y := by
    intro p hp
    simp only [U, V, Z, Y, primeBand, Finset.mem_union, Finset.mem_filter, hp,
      true_and, F] at *
    grind
  have hc : F.card ≤ U.card + V.card + Z.card + Y.card := calc
    _ ≤ _ := Finset.card_le_card hcover
    _ ≤ _ := by
      have h₁ := Finset.card_union_le U V
      have h₂ := Finset.card_union_le (U ∪ V) Z
      have h₃ := Finset.card_union_le (U ∪ V ∪ Z) Y
      omega
  have hu := small_count (by omega : 0 < k) hkn hw
  have hy := log_count (by omega : 0 < n-k) (Finset.filter_subset _ F)
    (by linarith : 0 < t) (fun p (hp : p ∈ Y) => (Finset.mem_filter.mp hp).2.le)
  have hy' : (Y.card : ℝ) ≤ b * Real.log k := by
    apply le_of_mul_le_mul_right _ (Real.log_pos ht)
    exact hy.trans ((Real.log_le_log (by exact_mod_cast (show 0 < n-k by omega))
      (by exact_mod_cast Nat.sub_le n k)).trans htail)
  rw [omega_eq]
  change (F.card : ℝ) ≤ _
  change (U.card : ℝ) ≤ _ at hu
  change (V.card : ℝ) ≤ _ at hmed
  change (Z.card : ℝ) ≤ _ at hlg
  have hc' : (F.card : ℝ) ≤ U.card + V.card + Z.card + Y.card := by exact_mod_cast hc
  linarith





/-- Count injective ordered tuples in the filtered set via falling factorials. -/
theorem count_tuples {P : Type*} [Fintype P] (hit : P → Prop) [DecidablePred hit] (s : ℕ) :
    (∑ f : Fin s → P, (if Function.Injective f ∧ ∀ i, hit (f i) then 1 else 0 : ℕ)) =
      (Fintype.card {p // hit p}).descFactorial s := by
  classical
  let e : {f : Fin s → P // Function.Injective f ∧ ∀ i, hit (f i)} ≃
      (Fin s ↪ {p // hit p}) :=
    { toFun := fun f => ⟨fun i => ⟨f.val i, f.property.2 i⟩,
          fun _ _ hij => f.property.1 (congrArg Subtype.val hij)⟩
      invFun := fun f => ⟨fun i => (f i).val,
        (fun _ _ hij => f.injective (Subtype.ext hij)), fun i => (f i).property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa [Fintype.card_subtype] using Fintype.card_congr e

/-- Transpose the two finite sums to apply Lau's joint-divisibility bounds. -/
theorem mean_factorial_eq {P : Type*} [Fintype P] (hit : ℕ → P → Prop)
    [∀ n, DecidablePred (hit n)] (S : Finset ℕ) (v : ℕ → ℝ) (s : ℕ) :
    ∑ n ∈ S, v n * ((Fintype.card {p // hit n p}).descFactorial s : ℕ) =
      ∑ f : Fin s → P, ∑ n ∈ S,
        (if Function.Injective f ∧ ∀ i, hit n (f i) then v n else 0) := by
  classical
  simp_rw [← count_tuples, Nat.cast_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro f _
  apply Finset.sum_congr rfl
  intro n _
  split <;> simp

theorem mean_factorial_le {P : Type*} [Fintype P] (hit : ℕ → P → Prop)
    [∀ n, DecidablePred (hit n)] (S : Finset ℕ) (v : ℕ → ℝ) (s : ℕ)
    (g : P → ℝ) (hg : ∀ p, 0 ≤ g p)
    (h : ∀ f : Fin s → P, Function.Injective f →
      ∑ n ∈ S, (if ∀ i, hit n (f i) then v n else 0) ≤ ∏ i, g (f i)) :
    ∑ n ∈ S, v n * ((Fintype.card {p // hit n p}).descFactorial s : ℕ) ≤
      (∑ p, g p) ^ s := by
  classical
  rw [mean_factorial_eq]
  calc
    _ ≤ ∑ f : Fin s → P, ∏ i, g (f i) := by
      apply sum_le_sum
      intro f _
      by_cases hf : Function.Injective f
      · simpa [hf] using h f hf
      · simp [hf, prod_nonneg (fun i _ => hg (f i))]
    _ = _ := by
      simpa using (Fintype.prod_sum (fun (_ : Fin s) (p : P) => g p)).symm


def intervalPrimes (r t : ℝ) := (Ioc ⌊r⌋₊ ⌊t⌋₊).filter Nat.Prime

theorem band_eq {r t : ℝ} (m : ℕ) :
    primeBand m r t = (intervalPrimes r t).filter (· ∈ m.primeFactors) := by
  ext p
  by_cases h : p ∈ m.primeFactors
  · have hp := Nat.prime_of_mem_primeFactors h
    simp only [primeBand, intervalPrimes, mem_filter, mem_Ioc, h, hp, true_and, and_true,
      Nat.floor_lt' hp.ne_zero, Nat.le_floor_iff' hp.ne_zero]
  · simp only [primeBand, mem_filter, h, false_and, and_false]

theorem band_card {r t : ℝ} (m : ℕ) :
    Fintype.card {p : intervalPrimes r t // p.val ∈ m.primeFactors} = (primeBand m r t).card := by
  rw [band_eq]
  let e : {p : intervalPrimes r t // p.val ∈ m.primeFactors} ≃
      ↥((intervalPrimes r t).filter (· ∈ m.primeFactors)) :=
    { toFun := fun p => ⟨p.val.val, mem_filter.mpr ⟨p.val.property, p.property⟩⟩
      invFun := fun p => ⟨⟨p.val, (mem_filter.mp p.property).1⟩, (mem_filter.mp p.property).2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  simpa only [Fintype.card_coe] using Fintype.card_congr e

/-- Lau's large-prime joint-divisibility estimate immediately gives the factorial moment. -/
theorem large_moment_of_joint {r t L : ℝ} {k s : ℕ} (hL : 0 ≤ L) (S : Finset ℕ) (v : ℕ → ℝ)
    (hv : ∀ n ∈ S, 0 ≤ v n)
    (h : ∀ f : Fin s → intervalPrimes r t, Function.Injective f →
      ∑ n ∈ S, (if ∀ i, (f i).val ∣ n-k then v n else 0) ≤ ∏ i, L / (f i).val) :
    ∑ n ∈ S, v n * ((primeBand (n-k) r t).card.descFactorial s : ℕ) ≤
      (L * ∑ p ∈ intervalPrimes r t, (1:ℝ)/p)^s := by
  have h' := mean_factorial_le (fun n (p : intervalPrimes r t) => p.val ∈ (n-k).primeFactors)
    S v s (fun p => L / p.val) (fun _ => div_nonneg hL (Nat.cast_nonneg _)) (by
      intro f hf
      refine le_trans (sum_le_sum (fun n hn => ?_)) (h f hf)
      by_cases he : ∀ i, (f i).val ∈ (n-k).primeFactors
      · have hd : ∀ i, (f i).val ∣ n-k := fun i => Nat.dvd_of_mem_primeFactors (he i)
        simp [he, hd]
      · simp only [if_neg he]
        split <;> simp [hv n hn])
  simp_rw [band_card] at h'
  convert h' using 1
  rw [mul_sum, ← Finset.sum_attach]
  congr 1
  apply sum_congr rfl
  intro p _
  ring

def order (k : ℕ) := Nat.log 2 k + 1

theorem order_le {k : ℕ} (hk : 2 ≤ k) : (order k : ℝ) ≤ 4 * Real.log k := by
  have hnat := Nat.pow_log_le_self 2 (show k ≠ 0 by omega)
  have hreal : (2 : ℝ) ^ Nat.log 2 k ≤ k := by exact_mod_cast hnat
  have hlog := Real.log_le_log (by positivity) hreal
  rw [Real.log_pow] at hlog
  have hc : 1/2 ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have hklog := Real.log_le_log (by norm_num) (show (2:ℝ) ≤ k by exact_mod_cast hk)
  simp only [order, Nat.cast_add, Nat.cast_one]
  nlinarith [mul_nonneg (show (0:ℝ) ≤ Nat.log 2 k by positivity) (sub_nonneg.mpr hc)]

def penalty (B k c : ℕ) : ℝ :=
  (c.descFactorial (order k) : ℝ) / (8 * (B : ℝ) * order k) ^ order k

theorem penalty_nonneg (B k c : ℕ) : 0 ≤ penalty B k c := by unfold penalty; positivity

theorem penalty_ge_one {B k c : ℕ} (hB : 0 < B) (h : (8 * B + 1) * order k ≤ c) :
    1 ≤ penalty B k c := by
  have hs : 0 < order k := Nat.succ_pos _
  unfold penalty
  apply (one_le_div (by positivity)).2
  have hbase : 8 * B * order k ≤ c + 1 - order k := by
    rw [Nat.add_mul, Nat.one_mul] at h
    omega
  exact_mod_cast (Nat.pow_le_pow_left hbase (order k)).trans (Nat.pow_sub_le_descFactorial c _)

theorem mean_penalty {S : Finset ℕ} {v : ℕ → ℝ} {c : ℕ → ℕ} {B k : ℕ} (hB : 0 < B)
    (h : ∑ n ∈ S, v n * (c n).descFactorial (order k) ≤ ((B : ℝ) * order k) ^ order k) :
    ∑ n ∈ S, v n * penalty B k (c n) ≤ 1 / (8:ℝ) ^ order k := by
  have hs : 0 < order k := Nat.succ_pos _
  simp only [penalty, ← mul_div_assoc, ← Finset.sum_div]
  rw [mul_assoc, mul_pow]
  have hpos : 0 < ((B : ℝ) * order k) ^ order k := by positivity
  apply (div_le_div_iff₀ (mul_pos (by positivity) hpos) (by positivity)).2
  linarith only [mul_le_mul_of_nonneg_right h (show 0 ≤ (8:ℝ) ^ order k by positivity),
    (mul_comm (((B:ℝ) * order k) ^ order k) ((8:ℝ)^order k))]

theorem budget (j : ℕ) : 2 / (8:ℝ) ^ order (j+2) ≤
    1 / ((j:ℝ)+1) - 1 / ((j:ℝ)+2) := by
  let s := order (j+2)
  have hk : (j:ℝ) + 2 ≤ (2:ℝ)^s := by
    exact_mod_cast (Nat.lt_pow_succ_log_self (by decide : 1 < 2) (j+2)).le
  have hs : 1 ≤ s := Nat.le_add_left 1 _
  have h₂ : (2:ℝ) ≤ 2^s := by simpa using
    (pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hs)
  have hsq := mul_le_mul hk hk (by positivity) (by positivity)
  have hcube := mul_le_mul h₂ hsq (by positivity) (by positivity)
  have h₈ : (8:ℝ)^s = 2^s * (2^s * 2^s) := by rw [← mul_pow, ← mul_pow]; norm_num
  change 2 / (8:ℝ)^s ≤ _
  rw [div_sub_div _ _ (by positivity : (j:ℝ)+1 ≠ 0) (by positivity : (j:ℝ)+2 ≠ 0)]
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  rw [h₈]
  nlinarith

theorem sum_budget (K : ℕ) : ∑ j ∈ range K, (1 / ((j:ℝ)+1) - 1 / ((j:ℝ)+2)) =
    1 - 1 / ((K:ℝ)+1) := by
  induction K with
  | zero => norm_num
  | succ K ih =>
    rw [sum_range_succ, ih]
    push_cast
    ring

/-- Two factorial moment bounds for each shift give a single center good for all shifts. -/
theorem extract_center {S : Finset ℕ} {v : ℕ → ℝ} {c d : ℕ → ℕ → ℕ} {B K : ℕ}
    (hB : 0 < B) (hv : ∀ n ∈ S, 0 ≤ v n) (hone : ∑ n ∈ S, v n = 1)
    (hc : ∀ j < K, ∑ n ∈ S, v n * (c n (j+2)).descFactorial (order (j+2)) ≤
      ((B:ℝ) * order (j+2)) ^ order (j+2))
    (hd : ∀ j < K, ∑ n ∈ S, v n * (d n (j+2)).descFactorial (order (j+2)) ≤
      ((B:ℝ) * order (j+2)) ^ order (j+2)) :
    ∃ n ∈ S, ∀ j < K, c n (j+2) < (8*B+1)*order (j+2) ∧
      d n (j+2) < (8*B+1)*order (j+2) := by
  let f := fun n j => penalty B (j+2) (c n (j+2)) + penalty B (j+2) (d n (j+2))
  have hf : ∀ n j, 0 ≤ f n j := fun _ _ => add_nonneg (penalty_nonneg ..) (penalty_nonneg ..)
  have hav : ∑ n ∈ S, v n * (∑ j ∈ range K, f n j) < 1 := calc
    _ = ∑ j ∈ range K, ∑ n ∈ S, v n * f n j := by simp_rw [Finset.mul_sum]; rw [sum_comm]
    _ ≤ ∑ j ∈ range K, (1 / ((j:ℝ)+1) - 1 / ((j:ℝ)+2)) := by
      apply sum_le_sum
      intro j hj
      simp only [f, mul_add, sum_add_distrib]
      have h := add_le_add (mean_penalty hB (hc j (mem_range.mp hj)))
        (mean_penalty hB (hd j (mem_range.mp hj)))
      rw [← add_div, one_add_one_eq_two] at h
      exact h.trans (budget j)
    _ < 1 := by
      rw [sum_budget]
      exact sub_lt_self _ (by positivity)
  obtain ⟨n, hn, hnlt⟩ : ∃ n ∈ S, (∑ j ∈ range K, f n j) < 1 := by
    by_contra! h
    have hle := sum_le_sum (s := S) (fun n hn => mul_le_mul_of_nonneg_left (h n hn) (hv n hn))
    simp only [mul_one, hone] at hle
    linarith
  refine ⟨n, hn, fun j hj => ?_⟩
  have hlt := lt_of_le_of_lt (single_le_sum (fun i _ => hf n i) (mem_range.mpr hj)) hnlt
  change penalty _ _ _ + penalty _ _ _ < 1 at hlt
  constructor <;> by_contra! h
  · linarith [penalty_ge_one hB h, penalty_nonneg B (j+2) (d n (j+2))]
  · linarith [penalty_ge_one hB h, penalty_nonneg B (j+2) (c n (j+2))]


/-- The upper prime cutoff has logarithm exactly log U / (b log k). -/
def cutoff (U b k : ℕ) : ℝ := Real.exp (Real.log U / (b * Real.log k))

/-- With U = Z^D the prescribed tuple fits within the CRT budget Z. -/
theorem forced_modulus {k D Z : ℕ} (hk : 2 ≤ k) (hD : 0 < D) (hZ : 2 ≤ Z)
    (f : Fin (order k) → ℕ) (hf : ∀ i, (f i : ℝ) ≤ cutoff (Z^D) (4*D) k) :
    (∏ i, f i) ≤ Z := by
  have hzR : (1:ℝ) < Z := by exact_mod_cast hZ
  have hkR : (1:ℝ) < k := by exact_mod_cast hk
  have hl := Real.log_pos hkR
  have hdR : (0:ℝ) < D := by exact_mod_cast hD
  have ht : 0 < cutoff (Z^D) (4*D) k := Real.exp_pos _
  have hr : (∏ i, (f i : ℝ)) ≤ (cutoff (Z^D) (4*D) k) ^ order k := by
    simpa using prod_le_prod (s := univ) (fun i _ => Nat.cast_nonneg (α := ℝ) (f i))
      (fun i _ => hf i)
  have hh : (cutoff (Z^D) (4*D) k) ^ order k ≤ (Z:ℝ) := by
    apply (Real.log_le_log_iff (pow_pos ht _) (by linarith)).mp
    rw [Real.log_pow, cutoff, Real.log_exp, Nat.cast_pow, Real.log_pow, Nat.cast_mul]
    push_cast
    rw [← mul_div_assoc]
    apply (div_le_iff₀ (by positivity)).mpr
    have h := mul_le_mul_of_nonneg_right (order_le hk)
      (mul_nonneg hdR.le (Real.log_pos hzR).le)
    linarith only [h]
  exact_mod_cast hr.trans hh

/-- Finite weighted data needed from the arithmetic sieve. The K shifts are 2 through K+1. -/
structure Window (N B b D : ℕ) where
  U : ℕ
  K : ℕ
  S : Finset ℕ
  v : ℕ → ℝ
  w : ℝ
  r : ℕ → ℝ
  upper_pos : 2 ≤ U
  large_shift : U ≤ (K+2)^D
  support : ∀ n ∈ S, N < n ∧ n ≤ U
  nonneg : ∀ n ∈ S, 0 ≤ v n
  mass : ∑ n ∈ S, v n = 1
  divisible : ∀ n ∈ S, ∀ p : ℕ, p.Prime → (p : ℝ) ≤ w → p ∣ n
  medium : ∀ j < K, ∑ n ∈ S, v n *
      ((primeBand (n-(j+2)) w (r (j+2))).card.descFactorial (order (j+2)) : ℕ) ≤
      ((B:ℝ) * order (j+2)) ^ order (j+2)
  large : ∀ j < K, ∑ n ∈ S, v n *
      ((primeBand (n-(j+2)) (r (j+2)) (cutoff U b (j+2))).card.descFactorial (order (j+2)) : ℕ) ≤
      ((B:ℝ) * order (j+2)) ^ order (j+2)

/-- Build the finite weighted window from a nonempty set of sifted centers. The only
large-prime count required is the joint count for exactly order k distinct primes. -/
theorem window_of_sifted {N B b D U K : ℕ} {w : ℝ} {r : ℕ → ℝ}
    (S : Finset ℕ) (hne : S.Nonempty) (hU : 2 ≤ U) (hfar : U ≤ (K+2)^D)
    (hsup : ∀ n ∈ S, N < n ∧ n ≤ U)
    (hw : ∀ n ∈ S, ∀ p : ℕ, p.Prime → (p:ℝ) ≤ w → p ∣ n)
    (hmed : ∀ n ∈ S, ∀ j < K, primeBand (n-(j+2)) w (r (j+2)) = ∅)
    {L : ℝ} (hL : 0 ≤ L)
    (hrecip : ∀ j < K, L * (∑ p ∈ intervalPrimes (r (j+2)) (cutoff U b (j+2)), (1:ℝ)/p) ≤
      B * (order (j+2) : ℝ))
    (hjoint : ∀ j < K, ∀ f : Fin (order (j+2)) → intervalPrimes (r (j+2)) (cutoff U b (j+2)),
      Function.Injective f → (((S.filter fun n => ∀ i, (f i).val ∣ n-(j+2)).card : ℝ)) ≤
        S.card * ∏ i, L / (f i).val) : Nonempty (Window N B b D) := by
  have hpos : (0:ℝ) < S.card := by exact_mod_cast card_pos.mpr hne
  refine ⟨{ U := U, K := K, S := S, v := fun _ => 1 / S.card, w := w, r := r,
            upper_pos := hU, large_shift := hfar, support := hsup,
            nonneg := fun _ _ => by positivity, mass := by simp [hpos.ne'],
            divisible := hw, medium := ?_, large := ?_ }⟩
  · intro j hj
    have hh (n) (hn : n ∈ S) := hmed n hn j hj
    have hz : ∀ n ∈ S, 1 / (S.card : ℝ) *
        ((primeBand (n-(j+2)) w (r (j+2))).card.descFactorial (order (j+2)) : ℕ) = 0 := by
      intro n hn
      simp [hh n hn, order, Nat.descFactorial_succ]
    rw [sum_eq_zero hz]
    positivity
  · intro j hj
    apply (large_moment_of_joint hL S (fun _ => 1 / S.card) (fun _ _ => by positivity) ?_).trans
    · apply pow_le_pow_left₀ _ (hrecip j hj)
      exact mul_nonneg hL (sum_nonneg (fun _ _ => by positivity))
    · intro f hf
      rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one_div, div_le_iff₀ hpos, mul_comm _ (S.card:ℝ)]
      exact hjoint j hj f hf

theorem h1_of_windows {B b D : ℕ} (hB : 0 < B) (hb : 0 < b)
    (windows : ∀ N, Nonempty (Window N B b D)) :
    OMA.R_Erdos413_erdos_413_parts_ii_R1.H1 := by
  let a : ℝ := (8*B+1:ℕ) * 4
  let C : ℝ := 2 + 2*a + b + 2*D
  have ha : 0 ≤ a := by dsimp [a]; positivity
  refine ⟨C, by dsimp [C]; positivity, {n | ∀ k : ℕ, 2 ≤ k → k < n →
    (ω (n-k) : ℝ) ≤ C * Real.log k}, ?_, fun _ hn => hn⟩
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨q⟩ := windows N
  obtain ⟨n, hn, h⟩ := extract_center (c := fun n k => (primeBand (n-k) q.w (q.r k)).card)
    (d := fun n k => (primeBand (n-k) (q.r k) (cutoff q.U b k)).card)
    hB q.nonneg q.mass q.medium q.large
  obtain ⟨hnN, hnU⟩ := q.support n hn
  refine ⟨n, ?_, hnN⟩
  intro k hk hkn
  have hk' : (1:ℝ) < k := by exact_mod_cast (show 1 < k by omega)
  have hl := Real.log_pos hk'
  by_cases hshort : k-2 < q.K
  · have hh := h (k-2) hshort
    rw [Nat.sub_add_cancel hk] at hh
    have convert_bound : ∀ c : ℕ, c < (8*B+1)*order k → (c : ℝ) ≤ a * Real.log k := by
      intro c hc
      have hcast : (c:ℝ) ≤ ((8*B+1:ℕ):ℝ) * (order k:ℝ) := by exact_mod_cast hc.le
      exact hcast.trans (by
        dsimp only [a]
        rw [mul_assoc]
        exact mul_le_mul_of_nonneg_left (order_le hk) (by positivity))
    have hden : 0 < (b : ℝ) * Real.log k := mul_pos (by exact_mod_cast hb) hl
    have hU : (1:ℝ) < q.U := by exact_mod_cast (show 1 < q.U from q.upper_pos)
    have ht : 1 < cutoff q.U b k := Real.one_lt_exp_iff.mpr (div_pos (Real.log_pos hU) hden)
    have htail : Real.log n ≤ (b:ℝ) * Real.log k * Real.log (cutoff q.U b k) := by
      rw [cutoff, Real.log_exp, mul_comm ((b:ℝ) * Real.log k), div_mul_cancel₀ _ hden.ne']
      exact Real.log_le_log (by exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast hnU)
    apply (log_four_ranges hk hkn (q.divisible n hn) ht htail
      (convert_bound _ hh.1) (convert_bound _ hh.2)).trans
    exact mul_le_mul_of_nonneg_right (by dsimp [C]; linarith [show (0:ℝ) ≤ D by positivity]) hl.le
  · have hnear : q.K+2 ≤ k := by omega
    have hpow := hnU.trans (q.large_shift.trans (Nat.pow_le_pow_left hnear D))
    have hnk : ((n-k:ℕ):ℝ) ≤ (k:ℝ)^D := by exact_mod_cast (Nat.sub_le n k).trans hpow
    have hlog := Real.log_le_log (by exact_mod_cast (show 0 < n-k by omega)) hnk
    rw [Real.log_pow] at hlog
    have hω := omega_log (by omega : 0 < n-k)
    calc
      _ ≤ 2 * ((D:ℝ) * Real.log k) := by linarith
      _ = (2*D:ℝ)*Real.log k := by ring
      _ ≤ C * Real.log k := by
        apply mul_le_mul_of_nonneg_right _ hl.le
        dsimp [C]
        linarith [show (0:ℝ) ≤ b by positivity]

end Lau413
end
open Finset
open scoped Classical
noncomputable section
namespace Lau413.Assembly
open Scales Brun
def blk (H h : ℕ) := (Ioc (level H (h+1)) (level H h)).filter Nat.Prime
def pool (H : ℕ) := (range H).biUnion (blk H)
theorem blk_mem {H h p} : p ∈ blk H h ↔ (level H (h+1) < p ∧ p ≤ level H h) ∧ p.Prime := by simp [blk]
theorem depth_lt {H h p} (hp : p ∈ blk H h) : h < H := by
  by_contra! hn
  have he : level H (h+1) = level H h := by simp [level,Nat.sub_eq_zero_of_le hn,Nat.sub_eq_zero_of_le (show H ≤ h+1 by omega)]
  have := (blk_mem.mp hp).1
  omega
theorem blk_sub (H h) : blk H h ⊆ pool H := fun _ hp => mem_biUnion.mpr ⟨h,mem_range.mpr (depth_lt hp),hp⟩
theorem disj (H i j) (hij : i ≠ j) : Disjoint (blk H i) (blk H j) := by
  apply disjoint_left.mpr
  intro p hi hj
  obtain ⟨⟨ai,bi⟩,_⟩ := blk_mem.mp hi
  obtain ⟨⟨aj,bj⟩,_⟩ := blk_mem.mp hj
  rcases lt_or_gt_of_ne hij with h | h
  · exact (ai.not_ge (bj.trans (level_antitone H h)))
  · exact (aj.not_ge (bi.trans (level_antitone H h)))
def depth (H p : ℕ) := if hp : ∃ h, p ∈ blk H h then Nat.find hp else 0
theorem depth_eq {H h p} (hp : p ∈ blk H h) : depth H p = h := by
  have he : ∃ h, p ∈ blk H h := ⟨h,hp⟩
  rw [depth,dif_pos he]
  by_contra hn
  exact disjoint_left.mp (disj H _ _ hn) (Nat.find_spec he) hp
def z (H) := level H 0
def samples (H) := (z H)^1000
def start (H) := Scales.primorial H * samples H
def center (H i) := start H + Scales.primorial H * i
def residues (H p : ℕ) := Icc 2 (2^depth H p)
def test (H) := hits (residues H) (start H) (Scales.primorial H)
def indices (H) := sift (test H) (pool H) (samples H)
theorem wlarge {H h p} (hp : p ∈ blk H h) : 2 * 2^h ≤ w H ∧ w H < p := by
  constructor
  · rw [mul_comm, ← pow_succ]
    exact Nat.pow_le_pow_right (by decide) (by have := depth_lt hp; omega)
  · exact (level_ge H _).trans_lt (blk_mem.mp hp).1.1
theorem cop {H p} (hp : p.Prime) (hw : w H < p) : (Scales.primorial H).Coprime p := by
  apply Nat.coprime_prod_left_iff.mpr
  intro q hq
  obtain ⟨hle,hprime⟩ := Nat.mem_primesLE.mp hq
  exact (Nat.coprime_primes hprime hp).mpr (by omega)
theorem count {H h p} (hp : p ∈ blk H h) : Brun.omega (test H) p ≤ 2^h := by
  obtain ⟨ha,hb⟩ := wlarge hp
  rw [test,hits_count _ (blk_mem.mp hp).2.pos (cop (blk_mem.mp hp).2 hb)]
  · simp [residues,depth_eq hp]
  · intro q hq
    have hq' : q ≤ 2^h := by simpa [residues,depth_eq hp] using (mem_Icc.mp hq).2
    exact mem_range.mpr (by omega)
def deg (h : ℕ) := 128 * 2^h
theorem even_deg (h) : Even (deg h) := ⟨64*2^h, by unfold deg; ring⟩
def model (Q : Finset ℕ) (g : ℕ → ℝ) := ∏ p ∈ Q, (1-g p / p)
def gfun (C : ℕ → ℕ → Prop) (p : ℕ) : ℝ := Brun.omega C p
def reciprocalOK (H : ℕ) := ∀ h, (∑ p ∈ blk H h, (1:ℝ)/p) ≤ 8
theorem recip_ok {H : ℕ} {y : ℝ} (hy : y ≤ w H)
    (hc : ∀ r ≥ y, (∑ p ∈ (Ioc ⌊r⌋₊ ⌊r^4⌋₊).filter Nat.Prime, (1:ℝ)/p) ≤ 8) : reciprocalOK H := by
  intro h
  by_cases hh : h < H
  · have hb := hc (level H (h+1)) (hy.trans (by exact_mod_cast level_ge H (h+1)))
    rw [← Nat.cast_pow, Nat.floor_natCast, Nat.floor_natCast, ← level_step hh] at hb
    exact hb
  · have he : blk H h = ∅ := eq_empty_iff_forall_notMem.mpr (fun _ hp => hh (depth_lt hp))
    simp [he]
theorem local_bounds {H h} {Q : Finset ℕ} {g : ℕ → ℝ} (hQ : Q ⊆ blk H h)
    (hg : ∀ p ∈ Q, 0 ≤ g p ∧ g p ≤ (2:ℝ)^h) :
    ∀ p ∈ Q, 0 ≤ g p / p ∧ g p / p ≤ 1/2 := by
  intro p hp
  obtain ⟨ha,hb⟩ := wlarge (hQ hp)
  have h2 : 2 * (2:ℝ)^h ≤ p := by exact_mod_cast ha.trans hb.le
  exact ⟨div_nonneg (hg p hp).1 (Nat.cast_nonneg _), (div_le_iff₀ (by exact_mod_cast (blk_mem.mp (hQ hp)).2.pos)).mpr (by linarith [(hg p hp).2])⟩
theorem local_mean {H h} {Q : Finset ℕ} {g : ℕ → ℝ} (hr : reciprocalOK H) (hQ : Q ⊆ blk H h)
    (hg : ∀ p ∈ Q, 0 ≤ g p ∧ g p ≤ (2:ℝ)^h) : ∑ p ∈ Q, g p / p ≤ 8*2^h := by
  calc
    _ ≤ ∑ p ∈ Q, (2:ℝ)^h * (1/p) := sum_le_sum fun p hp => by rw [mul_one_div]; exact div_le_div_of_nonneg_right (hg p hp).2 (Nat.cast_nonneg _)
    _ ≤ _ := by
      rw [← mul_sum,mul_comm (8:ℝ)]
      exact mul_le_mul_of_nonneg_left ((sum_le_sum_of_subset_of_nonneg hQ (fun _ _ _ => by positivity)).trans (hr h)) (by positivity)
theorem mod_pos {H h} {Q : Finset ℕ} {g : ℕ → ℝ} (hQ : Q ⊆ blk H h)
    (hg : ∀ p ∈ Q, 0 ≤ g p ∧ g p ≤ (2:ℝ)^h) : 0 < model Q g :=
  prod_pos fun p hp => by linarith [(local_bounds hQ hg p hp).2]
theorem eps_sum (H : ℕ) : ∑ h ∈ range H, 1/(2:ℝ)^(h+3) ≤ 1/2 := by
  suffices ∑ h ∈ range H, 1/(2:ℝ)^(h+3) + 1/(2:ℝ)^(H+2) = 1/4 by linarith [show 0 < 1/(2:ℝ)^(H+2) by positivity]
  induction H with
  | zero => norm_num
  | succ H ih =>
    rw [sum_range_succ]
    convert ih using 1
    ring_nf
theorem relative {H} (hr : reciprocalOK H) (Q : ℕ → Finset ℕ) (g : ℕ → ℝ)
    (hQ : ∀ h, Q h ⊆ blk H h) (hg : ∀ h p, p ∈ Q h → 0 ≤ g p ∧ g p ≤ (2:ℝ)^h) :
    ∑ h ∈ range H, dens g (Q h) (cE (deg h)) / model (Q h) g ≤ 1/2 := by
  apply le_trans _ (eps_sum H)
  apply sum_le_sum
  intro h _
  exact (div_le_iff₀ (mod_pos (hQ h) (hg h))).mpr (block_error _ _ h (local_bounds (hQ h) (hg h)) (local_mean hr (hQ h) (hg h)))
theorem mass_budget {H} (Q : ℕ → Finset ℕ) (g : ℕ → ℝ)
    (hQ : ∀ h, Q h ⊆ blk H h) (hg : ∀ h p, p ∈ Q h → 0 ≤ g p ∧ g p ≤ (2:ℝ)^h) :
    (∏ h ∈ range H, (mass g (Q h) (cU (deg h)) + mass g (Q h) (cE (deg h)))) ≤ (z H:ℝ)^774 := by
  have hmass (h c) : 0 ≤ mass g (Q h) c := sum_nonneg fun s hs => mul_nonneg (abs_nonneg _) (prod_nonneg fun p hp => (hg h p ((mem_powerset.mp hs) hp)).1)
  calc
    _ ≤ ∏ h ∈ range H, ((w H:ℝ) ^ ((387*2^h)*4^(H-h))) := by
      apply prod_le_prod (fun h _ => add_nonneg (hmass h _) (hmass h _))
      intro h _
      have hl := (w_two_le H).trans (level_ge H h)
      have hs : Q h ⊆ Icc 1 (level H h) := fun p hp => mem_Icc.mpr ⟨(blk_mem.mp (hQ h hp)).2.one_le,(blk_mem.mp (hQ h hp)).1.2⟩
      have hcard : (Q h).card ≤ level H h := by simpa using card_le_card hs
      apply (mass_bound _ hl hcard g (fun p hp => ⟨(hg h p hp).1, (hg h p hp).2.trans (by exact_mod_cast ((show 2^h ≤ w H by have := (wlarge (hQ h hp)).1; omega).trans (level_ge H h)))⟩) _).trans
      simp only [level, Nat.cast_pow, ← pow_mul]
      rw [mul_comm (387*2^h)]
      apply pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ w H by have := w_two_le H; omega))
      apply Nat.mul_le_mul_left
      unfold deg
      have : 0 < 2^h := by positivity
      omega
    _ ≤ _ := by
      rw [prod_pow_eq_pow_sum]
      simp only [z,level,Nat.sub_zero,Nat.cast_pow, ← pow_mul]
      apply pow_le_pow_right₀ (by exact_mod_cast (show 1 ≤ w H by have := w_two_le H; omega))
      simpa [Nat.mul_comm] using degree_cost H 387
end Lau413.Assembly

end
open Finset
open scoped Classical
noncomputable section
namespace Lau413.Assembly
open Scales Brun
def vblock (H h) := model (blk H h) (gfun (test H))
def volume (H) := ∏ h ∈ range H, vblock H h
theorem g_bound {H h p} (hp : p ∈ blk H h) : 0 ≤ gfun (test H) p ∧ gfun (test H) p ≤ (2:ℝ)^h :=
  ⟨Nat.cast_nonneg _,by unfold gfun; exact_mod_cast count hp⟩
theorem ztwo (H) : 2 ≤ z H := (w_two_le H).trans (level_ge H 0)
theorem zr (H) : (2:ℝ) ≤ z H := by exact_mod_cast ztwo H
theorem vp (H h) : 0 < vblock H h := mod_pos (Subset.rfl) (fun _ => g_bound)
theorem vol_lb {H} (hr : reciprocalOK H) : 1 ≤ (z H:ℝ)^16 * volume H := by
  have hsum : ∑ h ∈ range H, (2:ℝ)^h + 1 = 2^H := by
    clear hr
    induction H with
    | zero => simp
    | succ H ih => rw [sum_range_succ,pow_succ]; linarith
  have hw : 4 ≤ w H := Nat.pow_le_pow_right (n := 2) (by decide) (show 2 ≤ H+3 by omega)
  have hlog : 1 ≤ Real.log (w H) := by
    have a := Real.log_le_log (by norm_num : (0:ℝ)<4) (by exact_mod_cast hw : (4:ℝ) ≤ w H)
    rw [show (4:ℝ) = 2^2 by norm_num,Real.log_pow] at a
    norm_num at a
    linarith [Real.log_two_gt_d9]
  have hzlog : (2:ℝ)^H ≤ Real.log (z H) := by
    simp only [z,level,Nat.sub_zero,Nat.cast_pow,Real.log_pow]
    push_cast
    exact (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2) (by norm_num : (2:ℝ) ≤ 4) H).trans (le_mul_of_one_le_right (by positivity) hlog)
  have hlocal h : Real.exp (-(16*(2:ℝ)^h)) ≤ vblock H h := by
    let g := gfun (test H)
    have hg (p) (hp : p ∈ blk H h) := g_bound hp
    have hb := local_bounds (Q := blk H h) Subset.rfl hg
    have hm := local_mean hr Subset.rfl hg
    apply le_trans _ (V_ge_exp 1 (by norm_num) (fun p => g p / p) (blk H h) (fun p hp => ⟨(hb p hp).1, by dsimp [g]; linarith [(hb p hp).2]⟩))
    apply Real.exp_le_exp.mpr
    dsimp only [g]
    linarith
  have hv := prod_le_prod (s := range H) (fun h _ => Real.exp_nonneg (-(16*(2:ℝ)^h))) (fun h _ => hlocal h)
  rw [← Real.exp_sum, sum_neg_distrib, ← mul_sum] at hv
  have hpos : 0 < (z H:ℝ)^16 := by have := zr H; positivity
  rw [mul_comm]
  apply (div_le_iff₀ hpos).mp
  rw [one_div, ← Real.exp_log hpos, ← Real.exp_neg, Real.log_pow]
  exact (Real.exp_le_exp.mpr (by push_cast; linarith)).trans hv
theorem budget_main {H} (hr : reciprocalOK H) : 4 * (z H:ℝ)^775 ≤ samples H * volume H := by
  have hh := vol_lb hr
  have hz := zr H
  have hpow : 4 ≤ (z H:ℝ)^209 := calc
    (4:ℝ) ≤ (z H:ℝ)^2 := by nlinarith
    _ ≤ _ := pow_le_pow_right₀ (by linarith) (by decide)
  calc
    _ ≤ (z H:ℝ)^209 * (z H:ℝ)^775 := mul_le_mul_of_nonneg_right hpow (by positivity)
    _ = (z H:ℝ)^984 := by rw [← pow_add]
    _ ≤ (z H:ℝ)^984 * ((z H:ℝ)^16 * volume H) := le_mul_of_one_le_right (by positivity) hh
    _ = _ := by rw [← mul_assoc, ← pow_add]; simp [samples]
theorem pool_prime {H p} (hp : p ∈ pool H) : p.Prime := by
  obtain ⟨_,_,hb⟩ := mem_biUnion.mp hp
  exact (blk_mem.mp hb).2
theorem dbounds {H h} {Q : Finset ℕ} {g : ℕ → ℝ} (hq : Q ⊆ blk H h)
    (hg : ∀ p ∈ Q, 0 ≤ g p ∧ g p ≤ (2:ℝ)^h) :
    model Q g ≤ dens g Q (cU (deg h)) ∧ dens g Q (cU (deg h)) ≤ model Q g + dens g Q (cE (deg h)) :=
  density_bounds Q g (deg h) (even_deg h) (fun p hp => ⟨(local_bounds hq hg p hp).1,by linarith [(local_bounds hq hg p hp).2]⟩)
theorem lower {H} (hr : reciprocalOK H) : samples H * volume H / 4 ≤ ((indices H).card:ℝ) := by
  apply lower_comparison (test H) (pool H) (fun _ => pool_prime) (hits_periodic _ _ _) (blk H) H (blk_sub H) (disj H) _ deg even_deg _ (vblock H) (vp H)
  · intro h
    exact (dbounds (Q := blk H h) Subset.rfl (fun _ => g_bound)).1
  · exact relative hr _ _ (fun _ => Subset.rfl) (fun _ _ => g_bound)
  · apply (mass_budget _ _ (fun _ => Subset.rfl) (fun _ _ => g_bound (H := H))).trans
    have hb := budget_main hr
    change _ ≤ (samples H:ℝ) * volume H / 4
    have hp : (z H:ℝ)^774 ≤ (z H:ℝ)^775 := pow_le_pow_right₀ (by linarith [zr H]) (by decide)
    linarith
  · intro p hp
    simpa only [pool,mem_biUnion,mem_range] using hp
end Lau413.Assembly

end
open Finset
open scoped Classical
noncomputable section
namespace Lau413.Assembly
open Scales Brun
def remblk (H : ℕ) (R : Finset ℕ) (h : ℕ) := blk H h \ R
def fres (H k : ℕ) (R : Finset ℕ) (p : ℕ) := if p ∈ R then {k%p} else residues H p
def ftest (H k) (R : Finset ℕ) := hits (fres H k R) (start H) (Scales.primorial H)
theorem forced_g {H k p} {R : Finset ℕ} (hp : p ∈ R) (hp' : p.Prime) (hw : w H < p) :
    gfun (ftest H k R) p = 1 := by
  unfold gfun ftest
  rw [hits_count _ hp'.pos (cop hp' hw)]
  · simp [fres,hp]
  · simpa [fres,hp] using Nat.mod_lt k hp'.pos
theorem same_g {H k p} {R : Finset ℕ} (hp : p ∉ R) :
    gfun (ftest H k R) p = gfun (test H) p := by
  have he : ftest H k R p = test H p := by
    funext i
    simp [ftest,test,hits,fres,hp]
  simp only [gfun,Brun.omega,he]
theorem remvol {H k} (R : Finset ℕ) :
    (∏ h ∈ range H, model (remblk H R h) (gfun (ftest H k R))) ≤ (2:ℝ)^R.card * volume H := by
  let t := fun p => gfun (test H) p / p
  have eqr : (range H).biUnion (remblk H R) = pool H \ R := by
    ext p
    simp [remblk,pool]
    grind
  have heq (h) : model (remblk H R h) (gfun (ftest H k R)) = ∏ p ∈ remblk H R h, (1-t p) := by
    apply prod_congr rfl
    intro p hp
    rw [same_g (mem_sdiff.mp hp).2]
  have ht : ∀ p ∈ pool H, 0 ≤ t p ∧ t p ≤ 1/2 := by
    intro p hp
    obtain ⟨h,_,hb⟩ := mem_biUnion.mp hp
    exact local_bounds (Q := blk H h) Subset.rfl (fun _ => g_bound) p hb
  simp_rw [heq]
  have d : Set.PairwiseDisjoint (↑(range H)) (blk H) := fun i _ j _ hij => disj H i j hij
  have e : Set.PairwiseDisjoint (↑(range H)) (remblk H R) := fun i _ j _ hij => (disj H i j hij).mono sdiff_subset sdiff_subset
  rw [← prod_biUnion e,eqr]
  apply (density_without_forced _ _ t ht).trans_eq
  rw [pool,prod_biUnion d]
  rfl
theorem forced_est {H k} (hr : reciprocalOK H) (R : Finset ℕ)
    (hR : ∀ p ∈ R, p.Prime ∧ w H < p) (hd : (∏ p ∈ R, p) ≤ z H)
    (hk : ∀ i, k ≤ center H i) :
    (((indices H).filter fun i => ∀ p ∈ R, p ∣ center H i - k).card : ℝ) * (∏ p ∈ R, (p:ℝ)) ≤
      (indices H).card * (16 * (2:ℝ)^R.card) := by
  let C := ftest H k R
  let Q := remblk H R
  let g := gfun C
  let d := ∏ p ∈ R, (p:ℝ)
  have dq : ∀ h, Q h ⊆ blk H h := fun _ => sdiff_subset
  have hg : ∀ h p, p ∈ Q h → 0 ≤ g p ∧ g p ≤ (2:ℝ)^h := by
    intro h p hp
    dsimp only [g,C]
    rw [same_g (mem_sdiff.mp hp).2]
    exact g_bound (dq h hp)
  have hv h := mod_pos (dq h) (hg h)
  have hb h := dbounds (dq h) (hg h)
  have hupper := upper_main_term (range H) (fun h => model (Q h) g) (fun h => dens g (Q h) (cU (deg h))) (fun h => dens g (Q h) (cE (deg h))) (fun h _ => hv h) (fun h _ => (hv h).le.trans (hb h).1) (fun h _ => (hb h).2)
  have hx : Real.exp (∑ h ∈ range H, dens g (Q h) (cE (deg h))/model (Q h) g) ≤ 3 :=
    (Real.exp_le_exp.mpr ((relative hr Q g dq hg).trans (by norm_num))).trans Real.exp_one_lt_three.le
  have hupper' := hupper.trans (mul_le_mul hx (remvol (H:=H) (k:=k) R) (prod_nonneg (fun h _ => (hv h).le)) (by norm_num))
  have hmass (h c) : 0 ≤ mass g (Q h) c := sum_nonneg fun s hs => mul_nonneg (abs_nonneg _) (prod_nonneg fun p hp => (hg h p (mem_powerset.mp hs hp)).1)
  have herr := (prod_le_prod (fun h _ => hmass h (cU (deg h))) (fun h _ => le_add_of_nonneg_right (a := mass g (Q h) (cU (deg h))) (hmass h (cE (deg h))))).trans (mass_budget Q g dq hg)
  have hu := forced_upper C (pool H ∪ R) (fun p hp => (mem_union.mp hp).elim pool_prime (fun h => (hR p h).1)) (hits_periodic _ _ _) Q (fun h => (dq h).trans ((blk_sub H h).trans subset_union_left)) (fun i j hij => (disj H i j hij).mono (dq i) (dq j)) deg even_deg (samples H) H R subset_union_right (fun h _ => disjoint_left.mpr (fun _ hp hq => (mem_sdiff.mp hq).2 hp))
  have hsub : ((indices H).filter fun i => ∀ p ∈ R, p ∣ center H i - k) ⊆
      (range (samples H)).filter (fun i => (∀ p ∈ R, C p i) ∧ ∀ h < H, nu C (Q h) i = 0) := by
    intro i hi
    obtain ⟨hi,ht⟩ := mem_filter.mp hi
    obtain ⟨hi,hs⟩ := mem_filter.mp hi
    refine mem_filter.mpr ⟨hi,fun p hp => ?_,fun h hh => ?_⟩
    · have he := (Nat.modEq_of_dvd' (hk i) (ht p hp)).symm
      change center H i % p = k % p at he
      simpa [C,ftest,hits,fres,hp,center] using he
    · apply card_eq_zero.mpr
      apply eq_empty_iff_forall_notMem.mpr
      intro p hp
      obtain ⟨hp,hhit⟩ := mem_filter.mp hp
      apply hs p (blk_sub H h (dq h hp))
      simpa [C,ftest,test,hits,fres,(mem_sdiff.mp hp).2] using hhit
  have h1 (p) (hp : p ∈ R) : (Brun.omega C p:ℝ) = 1 := forced_g hp (hR p hp).1 (hR p hp).2
  have he1 : (∏ p ∈ R, (Brun.omega C p:ℝ)) = 1 := prod_eq_one h1
  have he2 : (∏ p ∈ R, ((Brun.omega C p:ℝ)/p)) = 1/d := by rw [prod_div_distrib,he1]
  rw [he1,he2,one_mul] at hu
  have hpos : 0 < d := prod_pos fun p hp => by exact_mod_cast (hR p hp).1.pos
  have dz : d ≤ z H := by dsimp only [d]; rw [← Nat.cast_prod]; exact_mod_cast hd
  have hcard := (show (((indices H).filter fun i => ∀ p ∈ R, p ∣ center H i - k).card : ℝ) ≤ _ by exact_mod_cast card_le_card hsub).trans hu
  have hxnn : 0 ≤ (samples H:ℝ)*(1/d) := by positivity
  have htotal := hcard.trans (add_le_add (mul_le_mul_of_nonneg_left hupper' hxnn) herr)
  have hmul := mul_le_mul_of_nonneg_right htotal hpos.le
  rw [add_mul] at hmul
  have hcan : (samples H:ℝ)*(1/d)*(3*(2^R.card*volume H))*d = (samples H:ℝ)*volume H*(3*2^R.card) := by field_simp
  rw [hcan] at hmul
  have hsmall : (z H:ℝ)^774 * d ≤ (z H:ℝ)^775 := (mul_le_mul_of_nonneg_left dz (by positivity)).trans_eq (pow_succ _ _).symm
  have hl := lower hr
  have he := budget_main hr
  have h1pow : (1:ℝ) ≤ 2^R.card := one_le_pow₀ (by norm_num)
  have hscore : (z H:ℝ)^775 ≤ ((indices H).card:ℝ) := by linarith
  have hscaled := mul_le_mul_of_nonneg_right (show (samples H:ℝ)*volume H ≤ 4*(indices H).card by linarith) (show (0:ℝ) ≤ 3*2^R.card by positivity)
  have hscale2 := mul_le_mul_of_nonneg_left h1pow (Nat.cast_nonneg (α:=ℝ) (indices H).card)
  linarith only [hmul,hsmall,hscore,hscaled,hscale2]
end Lau413.Assembly

end
open Finset
open scoped Classical
noncomputable section
namespace Lau413.Assembly
open Scales Brun
theorem wpos (H) : 0 < Scales.primorial H := Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun _ hp => (Nat.mem_primesLE.mp hp).2.ne_zero)
theorem zle_samples (H) : 2*z H ≤ samples H := calc
  _ ≤ z H * z H := Nat.mul_le_mul_right _ (ztwo H)
  _ = z H ^ 2 := (sq _).symm
  _ ≤ z H ^ 1000 := Nat.pow_le_pow_right (by have := ztwo H; omega) (by decide : 2 ≤ 1000)
theorem cle (H i) : samples H ≤ center H i := by
  unfold center start
  have := Nat.mul_le_mul_right (samples H) (show 1 ≤ Scales.primorial H from wpos H)
  simpa using this.trans (Nat.le_add_right _ _)
theorem cinj (H) : Function.Injective (center H) := by
  intro a b hab
  exact Nat.eq_of_mul_eq_mul_left (wpos H) (Nat.add_left_cancel hab)
def centers (H) := (indices H).image (center H)
theorem cne {H} (hr : reciprocalOK H) : (centers H).Nonempty := by
  apply Nonempty.image
  apply card_pos.mp
  have h := lower hr
  have h' := budget_main hr
  have hpos : 0 < (z H:ℝ)^775 := by have := zr H; positivity
  exact_mod_cast (show (0:ℝ) < (indices H).card by linarith)
theorem center_upper {H i} (hH : 3 ≤ H) (hi : i ∈ indices H) : center H i ≤ z H ^ 1002 := by
  have hi' := mem_range.mp (mem_filter.mp hi).1
  have hw := primorial_le_top hH
  calc
    _ ≤ Scales.primorial H * (2*samples H) := by rw [center,start,← Nat.mul_add]; gcongr; omega
    _ ≤ z H * (z H * samples H) := Nat.mul_le_mul hw (Nat.mul_le_mul_right _ (ztwo H))
    _ = _ := by unfold samples; ring
theorem shift_le {H j} (hj : j < z H) (i) : j+2 ≤ center H i := by
  have := zle_samples H
  have := cle H i
  have := ztwo H
  omega
theorem med {H j i} (hi : i ∈ indices H) (hj : j < z H) :
    primeBand (center H i-(j+2)) (w H) (level H (index (j+2))) = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro p hp
  obtain ⟨hpf,hl,hu⟩ := mem_filter.mp hp
  obtain ⟨h,_,ha,hb,hc⟩ := medium_covered (by exact_mod_cast hl) (by exact_mod_cast hu)
  have hb' := blk_mem.mpr ⟨⟨ha,hb⟩,Nat.prime_of_mem_primeFactors hpf⟩
  have hres := (Nat.modEq_of_dvd' (shift_le hj i) (Nat.dvd_of_mem_primeFactors hpf)).symm
  have hlp : j+2 < p := by have := wlarge hb'; omega
  apply (mem_filter.mp hi).2 p (blk_sub H h hb')
  change center H i % p ∈ residues H p
  rw [hres,Nat.mod_eq_of_lt hlp,residues,depth_eq hb']
  exact mem_Icc.mpr ⟨by omega,hc⟩
theorem joint {H j} (hr : reciprocalOK H) (hj : j < z H)
    (f : Fin (order (j+2)) → intervalPrimes (level H (index (j+2))) (cutoff (z H^1002) 4008 (j+2))) (hf : Function.Injective f) :
    (((centers H).filter fun n => ∀ i, (f i).val ∣ n-(j+2)).card : ℝ) ≤
      (centers H).card * ∏ i, 32 / ((f i).val:ℝ) := by
  let a := fun i => (f i).val
  let R := univ.image a
  have hi : Function.Injective a := Subtype.val_injective.comp hf
  have cardR : R.card = order (j+2) := by simp [R,card_image_of_injective _ hi]
  have pr (i) : (a i).Prime := (mem_filter.mp (f i).property).2
  have hb (i) := mem_Ioc.mp (mem_filter.mp (f i).property).1
  have hR : ∀ p ∈ R, p.Prime ∧ w H < p := by
    intro p hp
    obtain ⟨i,_,rfl⟩ := mem_image.mp hp
    refine ⟨pr i,(level_ge H (index (j+2))).trans_lt ?_⟩
    simpa [a] using (hb i).1
  have ht (i) : (a i:ℝ) ≤ cutoff (z H^1002) 4008 (j+2) :=
    (Nat.le_floor_iff (Real.exp_pos _).le).mp (hb i).2
  have dR : ∏ p ∈ R, p = ∏ i, a i := prod_image hi.injOn
  have fd := forced_est hr R hR (dR.trans_le (forced_modulus (by omega : 2 ≤ j+2) (by decide : 0 < 1002) (ztwo H) a ht)) (shift_le hj)
  have equiv (i) : (∀ p ∈ R, p ∣ center H i - (j+2)) ↔ ∀ l, a l ∣ center H i - (j+2) := by simp [R]
  simp_rw [equiv] at fd
  rw [centers,filter_image,card_image_of_injective _ (cinj H),card_image_of_injective _ (cinj H), prod_div_distrib,prod_const,card_univ,Fintype.card_fin]
  change _ ≤ _ * ((32:ℝ)^order (j+2) / ∏ l, (a l:ℝ))
  rw [← mul_div_assoc,le_div_iff₀ (prod_pos (fun i _ => by exact_mod_cast (pr i).pos))]
  rw [cardR,show (∏ p ∈ R, (p:ℝ)) = ∏ l, (a l:ℝ) from prod_image hi.injOn] at fd
  apply fd.trans
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  have ho : 1 ≤ order (j+2) := by unfold order; omega
  have h16 := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 16) ho
  rw [show (32:ℝ)=16*2 by norm_num,mul_pow]
  exact mul_le_mul_of_nonneg_right (by simpa using h16) (by positivity)
theorem finish : OMA.R_Erdos413_erdos_413_parts_ii_R1.H1 := by
  obtain ⟨y,L,_,hL,hlg⟩ := Reciprocals.large_prime_sum 1006
  obtain ⟨v,_,hblk⟩ := Reciprocals.fourth_power_block
  obtain ⟨B,hB⟩ := exists_nat_gt (32*L)
  have bp : 0 < B := by exact_mod_cast (show (0:ℝ) < B by linarith)
  apply h1_of_windows (B:=B) (b:=4008) (D:=1002) bp (by decide)
  intro N
  obtain ⟨M,hM⟩ := exists_nat_gt (max y v)
  let H := max 3 (max M (N+1))
  have h3 : 3 ≤ H := le_max_left _ _
  have hMH : M ≤ H := (le_max_left _ _).trans (le_max_right _ _)
  have hNH : N < H := (le_max_right _ _ : N+1 ≤ max M (N+1)).trans (le_max_right _ _)
  have hw : H ≤ w H := H.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) (by omega : H ≤ H+3))
  have hy : max y v ≤ w H := hM.le.trans (by exact_mod_cast hMH.trans hw)
  have hr := recip_ok ((le_max_right _ _).trans hy) hblk
  apply window_of_sifted (K:=z H) (U:=z H ^ 1002) (w:=w H) (r:=fun k => level H (index k)) (centers H) (cne hr) _ _ _ _ _ (L:=32) (by norm_num)
  · intro j hj
    have hk : 2 ≤ j+2 := by omega
    have hh := hlg (k:=j+2) (r:=(level H (index (j+2)):ℝ)) (t:=cutoff (z H^1002) 4008 (j+2)) hk (((le_max_left _ _).trans hy).trans (by exact_mod_cast level_ge H _)) (by
      rw [cutoff,Real.log_exp,Nat.cast_pow]
      exact large_interval_ratio H 1002 hk (by decide))
    have hn := Nat.lt_pow_succ_log_self (by decide : 1 < 2) (j+2)
    have hn' : ((j+2:ℕ):ℝ) ≤ (2:ℝ)^order (j+2) := by exact_mod_cast hn.le
    have hlog := Real.log_le_log (by positivity) hn'
    rw [Real.log_pow] at hlog
    have hlo : Real.log ((j+2:ℕ):ℝ) ≤ order (j+2) := hlog.trans (by
      apply mul_le_of_le_one_right (Nat.cast_nonneg _); linarith [Real.log_two_lt_d9])
    calc
      _ ≤ 32 * (L * Real.log ((j+2:ℕ):ℝ)) := mul_le_mul_of_nonneg_left hh (by norm_num)
      _ ≤ _ := by rw [← mul_assoc]; exact mul_le_mul hB.le hlo (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ j+2))) (Nat.cast_nonneg _)
  · exact fun j hj => joint hr hj
  · exact (ztwo H).trans ((pow_one (z H)).symm.le.trans (Nat.pow_le_pow_right (by have := ztwo H; omega) (by decide : 1 ≤ 1002)))
  · exact Nat.pow_le_pow_left (by omega) _
  · intro n hn
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    exact ⟨hNH.trans_le (hw.trans ((level_ge H 0).trans ((show z H ≤ samples H by have := zle_samples H; omega).trans (cle H i)))), center_upper h3 hi⟩
  · intro n hn p hp hpw
    obtain ⟨i,_,rfl⟩ := mem_image.mp hn
    rw [center,start,← Nat.mul_add]
    exact dvd_mul_of_dvd_left (prime_dvd_primorial hp (by exact_mod_cast hpw)) _
  · intro n hn j hj
    obtain ⟨i,hi,rfl⟩ := mem_image.mp hn
    exact med hi hj
end Lau413.Assembly

theorem OMA.solution : OMA.R_Erdos413_erdos_413_parts_ii_R1.H1 := by
  exact Lau413.Assembly.finish

end
