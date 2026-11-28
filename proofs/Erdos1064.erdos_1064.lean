import FormalConjectures.ErdosProblems.«1064»


open Filter Set Topology

namespace OMA1064

open scoped Classical

noncomputable def cnt (S : Set ℕ) (b : ℕ) : ℕ := ((Finset.range b).filter (· ∈ S)).card

lemma pd_eq (S : Set ℕ) (b : ℕ) : S.partialDensity Set.univ b = (cnt S b : ℝ) / b := by
  simp only [Set.partialDensity, Set.inter_univ, Set.univ_inter]
  have h1 : S ∩ Iio b = ↑((Finset.range b).filter (· ∈ S)) := by
    ext n; simp [and_comm]
  rw [h1, Set.ncard_coe_finset, Nat.ncard_Iio]
  simp [cnt]

lemma hasDensity_iff (S : Set ℕ) (d : ℝ) :
    S.HasDensity d ↔ Tendsto (fun b => (cnt S b : ℝ) / b) atTop (𝓝 d) := by
  simp only [Set.HasDensity, pd_eq]

lemma cnt_succ (S : Set ℕ) (n : ℕ) :
    cnt S (n + 1) = cnt S n + (if n ∈ S then 1 else 0) := by
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.card_insert_of_notMem (by simp)]
  · simp

lemma cnt_le (S : Set ℕ) (n : ℕ) : cnt S n ≤ n := by
  unfold cnt
  exact (Finset.card_filter_le _ _).trans (by simp)

lemma cnt_mono {S T : Set ℕ} (h : S ⊆ T) (n : ℕ) : cnt S n ≤ cnt T n := by
  unfold cnt
  exact Finset.card_le_card (fun x hx => by
    simp only [Finset.mem_filter] at hx ⊢; exact ⟨hx.1, h hx.2⟩)

lemma cnt_union_le (S T : Set ℕ) (n : ℕ) : cnt (S ∪ T) n ≤ cnt S n + cnt T n := by
  unfold cnt
  refine (Finset.card_le_card ?_).trans (Finset.card_union_le _ _)
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hx ⊢
  tauto

lemma cnt_split (S X : Set ℕ) (n : ℕ) : cnt S n = cnt (S ∩ X) n + cnt (S \ X) n := by
  unfold cnt
  rw [← Finset.card_union_of_disjoint]
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_union, Set.mem_inter_iff,
      Set.mem_sdiff]; tauto
  · rw [Finset.disjoint_left]; intro x h1 h2
    simp only [Finset.mem_filter, Set.mem_inter_iff, Set.mem_sdiff] at h1 h2; tauto

def Per (Y : Set ℕ) (N : ℕ) : Prop := ∀ n, n ∈ Y ↔ n + N ∈ Y

lemma Per.mem_add_mul {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n k : ℕ) :
    n ∈ Y ↔ n + N * k ∈ Y := by
  induction k with
  | zero => simp
  | succ k ih => rw [ih, h (n + N * k)]; ring_nf

lemma Per.mem_mod {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) : n ∈ Y ↔ n % N ∈ Y := by
  rw [h.mem_add_mul (n % N) (n / N), Nat.mod_add_div]

lemma Per.cnt_add {Y : Set ℕ} {N : ℕ} (h : Per Y N) (n : ℕ) :
    cnt Y (n + N) = cnt Y n + cnt Y N := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    rw [show n + 1 + N = (n + N) + 1 by ring, cnt_succ, ih, cnt_succ]
    have := h n
    by_cases hn : n ∈ Y
    · rw [if_pos hn, if_pos (this.1 hn)]; omega
    · rw [if_neg hn, if_neg (fun h' => hn (this.2 h'))]; omega

lemma Per.cnt_approx {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) (n : ℕ) :
    |(cnt Y n : ℝ) - n * (cnt Y N) / N| ≤ N := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hn : n < N
    · have h1 : (cnt Y n : ℝ) ≤ n := by exact_mod_cast cnt_le Y n
      have h2 : (cnt Y N : ℝ) ≤ N := by exact_mod_cast cnt_le Y N
      have hN' : (0 : ℝ) < N := by exact_mod_cast hN
      have h3 : (n : ℝ) * cnt Y N / N ≤ n := by
        rw [div_le_iff₀ hN']; exact mul_le_mul_of_nonneg_left h2 (by positivity)
      have h4 : (0 : ℝ) ≤ n * cnt Y N / N := by positivity
      have h5 : (n : ℝ) ≤ N := by exact_mod_cast hn.le
      rw [abs_le]; constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) (cnt Y n)]
    · obtain ⟨m, rfl⟩ : ∃ m, n = m + N := ⟨n - N, by omega⟩
      have := ih m (by omega)
      rw [h.cnt_add]
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have e : ((cnt Y m + cnt Y N : ℕ) : ℝ) - ((m + N : ℕ) : ℝ) * cnt Y N / N
          = (cnt Y m : ℝ) - m * cnt Y N / N := by
        push_cast; field_simp; ring
      rw [e]; exact this

lemma Per.hasDensity {Y : Set ℕ} {N : ℕ} (h : Per Y N) (hN : 0 < N) :
    Y.HasDensity ((cnt Y N : ℝ) / N) := by
  rw [hasDensity_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n0, hn0⟩ := exists_nat_gt ((N : ℝ) / ε)
  refine ⟨n0 + 1, fun n hn => ?_⟩
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hn' : (N : ℝ) / ε < n := lt_of_lt_of_le hn0 (by exact_mod_cast (show n0 ≤ n by omega))
  rw [Real.dist_eq]
  have e : (cnt Y n : ℝ) / n - cnt Y N / N = ((cnt Y n : ℝ) - n * cnt Y N / N) / n := by
    field_simp
  rw [e, abs_div, abs_of_pos hnpos, div_lt_iff₀ hnpos]
  refine lt_of_le_of_lt (h.cnt_approx hN n) ?_
  rwa [div_lt_iff₀ hε, mul_comm] at hn'

lemma HasDensity.unique {S : Set ℕ} {a b : ℝ} (ha : S.HasDensity a) (hb : S.HasDensity b) :
    a = b := tendsto_nhds_unique ha hb

lemma HasDensity.diff {S X : Set ℕ} {a b : ℝ} (ha : S.HasDensity a)
    (hb : (S ∩ X).HasDensity b) : (S \ X).HasDensity (a - b) := by
  rw [hasDensity_iff] at *
  refine (ha.sub hb).congr (fun n => ?_)
  rw [cnt_split S X n]; push_cast; ring

/-- Key CRT counting: multiples of a coprime `p` in a periodic set. -/
lemma Per.cnt_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) (hN : 0 < N) (hp : 0 < p)
    (hc : Nat.Coprime p N) : cnt (Y ∩ {n | p ∣ n}) (p * N) = cnt Y N := by
  unfold cnt
  have e1 : (Finset.range (p * N)).filter (· ∈ Y ∩ {n | p ∣ n}) =
      ((Finset.range N).filter (fun k => p * k ∈ Y)).image (p * ·) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Set.mem_inter_iff, Set.mem_setOf_eq,
      Finset.mem_image]
    constructor
    · rintro ⟨h1, h2, k, rfl⟩
      exact ⟨k, ⟨by nlinarith, h2⟩, rfl⟩
    · rintro ⟨k, ⟨h1, h2⟩, rfl⟩
      exact ⟨by nlinarith, h2, dvd_mul_right _ _⟩
  refine Eq.trans (b := (((Finset.range N).filter (fun k => p * k ∈ Y)).image (p * ·)).card)
    (by convert congrArg Finset.card e1) ?_
  rw [Finset.card_image_of_injective _ (fun a b hab => by
    simpa [hp.ne'] using hab)]
  -- bijection k ↦ p*k % N
  have hinj : ∀ a ∈ Finset.range N, ∀ b ∈ Finset.range N, p * a % N = p * b % N → a = b := by
    intro a ha b hb hab
    simp only [Finset.mem_range] at ha hb
    have h1 : p * a ≡ p * b [MOD N] := hab
    have h2 := Nat.ModEq.cancel_left_of_coprime (by rw [Nat.gcd_comm]; exact hc) h1
    unfold Nat.ModEq at h2
    rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at h2
  have himg : (Finset.range N).image (fun k => p * k % N) = Finset.range N := by
    apply Finset.eq_of_subset_of_card_le
    · intro x hx; simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
      obtain ⟨k, -, rfl⟩ := hx; exact Nat.mod_lt _ hN
    · rw [Finset.card_image_of_injOn (fun a ha b hb hab => hinj a ha b hb hab)]
  apply Finset.card_nbij (fun k => p * k % N)
  · intro k hk
    have hk' := Finset.mem_filter.1 hk
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 (Nat.mod_lt _ hN), (h.mem_mod _).1 hk'.2⟩
  · intro a ha b hb hab
    have ha' := Finset.mem_filter.1 (Finset.mem_coe.1 ha)
    have hb' := Finset.mem_filter.1 (Finset.mem_coe.1 hb)
    exact hinj a ha'.1 b hb'.1 hab
  · intro m hm
    have hm' := Finset.mem_filter.1 (Finset.mem_coe.1 hm)
    have : m ∈ (Finset.range N).image (fun k => p * k % N) := by
      rw [himg]; exact hm'.1
    obtain ⟨k, hk, hkm⟩ := Finset.mem_image.1 this
    refine ⟨k, Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hk, ?_⟩), hkm⟩
    rw [h.mem_mod, hkm]; exact hm'.2

lemma Per.inter_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) :
    Per (Y ∩ {n | p ∣ n}) (p * N) := by
  intro n
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq]
  rw [h.mem_add_mul n p, mul_comm N p, Nat.dvd_add_left (dvd_mul_right p N)]

lemma Per.hasDensity_dvd {Y : Set ℕ} {N p : ℕ} (h : Per Y N) (hN : 0 < N) (hp : 0 < p)
    (hc : Nat.Coprime p N) {d : ℝ} (hd : Y.HasDensity d) :
    (Y ∩ {n | p ∣ n}).HasDensity (d / p) := by
  have e := HasDensity.unique hd (h.hasDensity hN)
  have := (h.inter_dvd (p := p)).hasDensity (Nat.mul_pos hp hN)
  rw [h.cnt_dvd hN hp hc] at this
  convert this using 1
  rw [e]; push_cast; field_simp

/-! ## The finite model -/

def status (Q : Finset ℕ) (n : ℕ) : Finset ℕ := Q.filter (· ∣ n)

noncomputable def g (D : Finset ℕ) : ℝ := ∏ p ∈ D, (1 - 1 / (p : ℝ))

noncomputable def w (Q D : Finset ℕ) : ℝ :=
  (∏ p ∈ D, 1 / (p : ℝ)) * ∏ p ∈ Q \ D, (1 - 1 / (p : ℝ))

lemma one_sub_nonneg' (p : ℕ) : 0 ≤ 1 - 1 / (p : ℝ) := by
  rcases Nat.eq_zero_or_pos p with h | h
  · simp [h]
  · have : (1 : ℝ) / p ≤ 1 := by
      rw [div_le_one (by exact_mod_cast h)]; exact_mod_cast h
    linarith

lemma g_nonneg (D : Finset ℕ) : 0 ≤ g D := Finset.prod_nonneg fun p _ => one_sub_nonneg' p

lemma g_insert {p : ℕ} {E : Finset ℕ} (h : p ∉ E) : g (insert p E) = (1 - 1 / (p : ℝ)) * g E := by
  unfold g; rw [Finset.prod_insert h]

lemma status_per (Q : Finset ℕ) (R : Finset ℕ → Prop) :
    Per {n | R (status Q n)} (∏ p ∈ Q, p) := by
  intro n
  simp only [Set.mem_setOf_eq]
  have : status Q (n + ∏ p ∈ Q, p) = status Q n := by
    unfold status
    refine Finset.filter_congr fun p hp => ?_
    exact Nat.dvd_add_left (Finset.dvd_prod_of_mem _ hp)
  rw [this]

lemma prod_pos_of_primes (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) : 0 < ∏ p ∈ Q, p :=
  Finset.prod_pos fun p hp => (hQ p hp).pos

lemma status_insert {p : ℕ} {Q : Finset ℕ} (n : ℕ) :
    status (insert p Q) n = if p ∣ n then insert p (status Q n) else status Q n := by
  unfold status; rw [Finset.filter_insert]

lemma density_status (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    ∀ D ⊆ Q, {n | status Q n = D}.HasDensity (w Q D) := by
  induction Q using Finset.induction_on with
  | empty =>
    intro D hD
    rw [Finset.subset_empty] at hD
    subst hD
    have : {n | status ∅ n = (∅ : Finset ℕ)} = Set.univ := by
      ext n; simp [status]
    rw [this]
    simp [w]
  | insert p Q hpQ ih =>
    intro D hD
    have hp : p.Prime := hQ p (Finset.mem_insert_self p Q)
    have hQ' : ∀ q ∈ Q, q.Prime := fun q hq => hQ q (Finset.mem_insert_of_mem hq)
    have hcop : Nat.Coprime p (∏ q ∈ Q, q) := by
      refine Nat.Coprime.prod_right fun q hq => ?_
      exact (Nat.coprime_primes hp (hQ' q hq)).2 (fun h => hpQ (h ▸ hq))
    have hN := prod_pos_of_primes Q hQ'
    have hpS : ∀ n, p ∉ status Q n := fun n h => hpQ (Finset.mem_filter.1 h).1
    by_cases hpD : p ∈ D
    · have hE : D.erase p ⊆ Q := by
        intro x hx
        have := Finset.mem_erase.1 hx
        rcases Finset.mem_insert.1 (hD this.2) with h | h
        · exact absurd h this.1
        · exact h
      have hset : {n | status (insert p Q) n = D} =
          {n | status Q n = D.erase p} ∩ {n | p ∣ n} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_inter_iff, status_insert]
        by_cases hn : p ∣ n
        · rw [if_pos hn]
          constructor
          · intro h; refine ⟨?_, hn⟩; rw [← h, Finset.erase_insert (hpS n)]
          · intro h; rw [h.1, Finset.insert_erase hpD]
        · rw [if_neg hn]
          constructor
          · intro h; exact absurd (h ▸ hpD) (hpS n)
          · intro h; exact absurd h.2 hn
      rw [hset]
      have := (status_per Q (· = D.erase p)).hasDensity_dvd hN hp.pos hcop (ih hQ' _ hE)
      convert this using 1
      unfold w
      rw [← Finset.mul_prod_erase D _ hpD]
      have : insert p Q \ D = Q \ D.erase p := by
        ext x
        simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact absurd (h1 ▸ hpD) h2
          · exact ⟨h1, fun h => h2 h.2⟩
        · rintro ⟨h1, h2⟩
          refine ⟨Or.inr h1, fun h => h2 ⟨?_, h⟩⟩
          rintro rfl; exact hpQ h1
      rw [this]; ring
    · have hD' : D ⊆ Q := by
        intro x hx
        rcases Finset.mem_insert.1 (hD hx) with h | h
        · exact absurd (h ▸ hx) hpD
        · exact h
      have hset : {n | status (insert p Q) n = D} =
          {n | status Q n = D} \ {n | p ∣ n} := by
        ext n
        simp only [Set.mem_setOf_eq, Set.mem_sdiff, status_insert]
        by_cases hn : p ∣ n
        · rw [if_pos hn]
          constructor
          · intro h; exact absurd (h ▸ Finset.mem_insert_self p _) hpD
          · intro h; exact absurd hn h.2
        · rw [if_neg hn]; tauto
      rw [hset]
      have h1 := ih hQ' D hD'
      have h2 := (status_per Q (· = D)).hasDensity_dvd hN hp.pos hcop h1
      have := HasDensity.diff h1 h2
      convert this using 1
      unfold w
      have : insert p Q \ D = insert p (Q \ D) := by
        ext x; simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨h1 | h1, h2⟩
          · exact Or.inl h1
          · exact Or.inr ⟨h1, h2⟩
        · rintro (h1 | ⟨h1, h2⟩)
          · exact ⟨Or.inl h1, h1 ▸ hpD⟩
          · exact ⟨Or.inr h1, h2⟩
      rw [this, Finset.prod_insert (fun h => hpQ (Finset.mem_sdiff.1 h).1)]
      ring

/-! ## Number theory bridge -/

lemma phi_eq {n : ℕ} (hn : n ≠ 0) :
    (Nat.totient n : ℝ) = n * ∏ p ∈ n.primeFactors, (1 - 1 / (p : ℝ)) := by
  have h := congrArg (Rat.cast : ℚ → ℝ) (Nat.totient_eq_mul_prod_factors n)
  push_cast at h
  simpa [one_div] using h

noncomputable def hK (K n : ℕ) : ℝ := ∑ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), 1 / (p : ℝ)

noncomputable def QK (K : ℕ) : Finset ℕ := (Finset.range (K + 1)).filter Nat.Prime

lemma QK_prime (K : ℕ) : ∀ p ∈ QK K, p.Prime := fun p hp => (Finset.mem_filter.1 hp).2

lemma prod_ge (s : Finset ℕ) : 1 - ∑ p ∈ s, 1 / (p : ℝ) ≤ ∏ p ∈ s, (1 - 1 / (p : ℝ)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    have h0 := one_sub_nonneg' a
    have hy : 0 ≤ ∑ p ∈ s, 1 / (p : ℝ) := Finset.sum_nonneg fun p _ => by positivity
    have hx : 0 ≤ 1 / (a : ℝ) := by positivity
    have : (1 - 1 / (a : ℝ)) * (1 - ∑ p ∈ s, 1 / (p : ℝ)) ≤
        (1 - 1 / (a : ℝ)) * ∏ p ∈ s, (1 - 1 / (p : ℝ)) := mul_le_mul_of_nonneg_left ih h0
    nlinarith

lemma phi_split {n : ℕ} (hn : n ≠ 0) (K : ℕ) :
    (Nat.totient n : ℝ) = n * (g (status (QK K) n) *
      ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ))) := by
  rw [phi_eq hn, ← Finset.prod_filter_mul_prod_filter_not n.primeFactors (fun p => p ≤ K)]
  congr 2
  unfold g status QK
  congr 1
  ext p
  simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2, _⟩, h4⟩; exact ⟨⟨by omega, h1⟩, h2⟩
  · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h2, h3, hn⟩, by omega⟩

/-! ## The bad set -/

lemma tail_sq (K : ℕ) (hK : 1 ≤ K) (N : ℕ) :
    ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
  have key : ∀ j : ℕ, ∑ m ∈ (Finset.range (j + K + 1)).filter (fun m => ¬ m ≤ K),
      1 / (m : ℝ) ^ 2 ≤ 1 / (K : ℝ) - 1 / ((j + K : ℕ) : ℝ) := by
    intro j
    induction j with
    | zero =>
      have : (Finset.range (0 + K + 1)).filter (fun m => ¬ m ≤ K) = ∅ := by
        rw [Finset.filter_eq_empty_iff]; intro m hm; simp only [Finset.mem_range] at hm; omega
      rw [this]; simp
    | succ j ih =>
      rw [show j + 1 + K + 1 = (j + K + 1) + 1 by ring, Finset.range_add_one,
        Finset.filter_insert, if_pos (by omega),
        Finset.sum_insert (by simp)]
      have hK' : (1 : ℝ) ≤ K := by exact_mod_cast hK
      have hjK : (0 : ℝ) < (j + K : ℕ) := by push_cast; positivity
      have e : 1 / (((j + K + 1 : ℕ) : ℝ)) ^ 2 ≤ 1 / ((j + K : ℕ) : ℝ) - 1 / ((j + 1 + K : ℕ) : ℝ) := by
        push_cast
        rw [div_sub_div _ _ (by positivity) (by positivity), div_le_div_iff₀ (by positivity)
          (by positivity)]
        nlinarith
      linarith
  have hsub : (Finset.range N).filter (fun m => ¬ m ≤ K) ⊆
      (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K) :=
    Finset.filter_subset_filter _ (Finset.range_subset_range.2 (by omega))
  calc _ ≤ ∑ m ∈ (Finset.range (N + K + 1)).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ ≤ 1 / (K : ℝ) - 1 / ((N + K : ℕ) : ℝ) := key N
    _ ≤ 1 / (K : ℝ) := by
        have : (0 : ℝ) ≤ 1 / ((N + K : ℕ) : ℝ) := by positivity
        linarith

lemma card_mult_le (p N : ℕ) (hp : 0 < p) :
    (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ N / p := by
  have h : (Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0) ⊆
      (Finset.Icc 1 (N / p)).image (p * ·) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    obtain ⟨hnN, ⟨k, rfl⟩, hn0⟩ := hn
    simp only [Finset.mem_image, Finset.mem_Icc]
    refine ⟨k, ⟨?_, ?_⟩, rfl⟩
    · rcases Nat.eq_zero_or_pos k with h | h
      · simp [h] at hn0
      · exact h
    · rw [Nat.le_div_iff_mul_le hp]; linarith
  have h1 := Finset.card_le_card h
  have h2 := Finset.card_image_le (s := Finset.Icc 1 (N / p)) (f := (p * ·))
  simp only [Nat.card_Icc, add_tsub_cancel_right] at h2
  have h3 : ((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card ≤ N / p := h1.trans h2
  calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) ≤ ((N / p : ℕ) : ℝ) := by
        exact_mod_cast h3
    _ ≤ N / p := Nat.cast_div_le

lemma sum_hK (K N : ℕ) (hK1 : 1 ≤ K) : ∑ n ∈ Finset.range N, hK K n ≤ N / K := by
  have e1 : ∀ n ∈ Finset.range N, hK K n = ∑ p ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0 := by
    intro n hn
    rw [← Finset.sum_filter]
    unfold hK
    congr 1
    ext p
    simp only [Finset.mem_filter, Nat.mem_primeFactors, Finset.mem_range] at hn ⊢
    constructor
    · rintro ⟨⟨h1, h2, h3⟩, h4⟩
      exact ⟨lt_of_le_of_lt (Nat.le_of_dvd (Nat.pos_of_ne_zero h3) h2) hn, ⟨h1, h4⟩, h2, h3⟩
    · rintro ⟨_, ⟨h1, h4⟩, h2, h3⟩; exact ⟨⟨h1, h2, h3⟩, h4⟩
  rw [Finset.sum_congr rfl e1, Finset.sum_comm]
  have e2 : ∀ p ∈ Finset.range N, (∑ n ∈ Finset.range N,
      if (p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0) then 1 / (p : ℝ) else 0) ≤
      if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0 := by
    intro p _
    by_cases hp : p.Prime ∧ ¬ p ≤ K
    · have hiff : ∀ n, ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) ↔ (p ∣ n ∧ n ≠ 0) :=
        fun n => ⟨fun h => h.2, fun h => ⟨hp, h⟩⟩
      rw [if_pos hp.2, Finset.sum_congr rfl (fun n _ => if_congr (hiff n) rfl rfl),
        ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
      have := card_mult_le p N hp.1.pos
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.1.pos
      calc (((Finset.range N).filter (fun n => p ∣ n ∧ n ≠ 0)).card : ℝ) * (1 / p)
          ≤ (N / p) * (1 / p) := mul_le_mul_of_nonneg_right this (by positivity)
        _ = N * (1 / (p : ℝ) ^ 2) := by field_simp
    · have : ∀ n, ¬ ((p.Prime ∧ ¬ p ≤ K) ∧ (p ∣ n ∧ n ≠ 0)) := fun n h => hp h.1
      simp only [this, if_false, Finset.sum_const_zero]
      split_ifs <;> positivity
  calc _ ≤ ∑ p ∈ Finset.range N, (if ¬ p ≤ K then N * (1 / (p : ℝ) ^ 2) else 0) :=
        Finset.sum_le_sum e2
    _ = N * ∑ m ∈ (Finset.range N).filter (fun m => ¬ m ≤ K), 1 / (m : ℝ) ^ 2 := by
        rw [Finset.mul_sum, Finset.sum_filter]
    _ ≤ N * (1 / K) := mul_le_mul_of_nonneg_left (tail_sq K hK1 N) (by positivity)
    _ = N / K := by ring

lemma cnt_bad (K N : ℕ) (hK1 : 1 ≤ K) {δ : ℝ} (hδ : 0 < δ) :
    (cnt {n | δ < hK K n} N : ℝ) ≤ N / (K * δ) := by
  have hnn : ∀ n, 0 ≤ hK K n := fun n => Finset.sum_nonneg fun p _ => by positivity
  have h1 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ ∑ n ∈ Finset.range N, hK K n := by
    unfold cnt
    calc (((Finset.range N).filter (· ∈ {n | δ < hK K n})).card : ℝ) * δ
        = ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), δ := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ n ∈ (Finset.range N).filter (· ∈ {n | δ < hK K n}), hK K n :=
          Finset.sum_le_sum fun n hn => (Finset.mem_filter.1 hn).2.le
      _ ≤ ∑ n ∈ Finset.range N, hK K n :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun n _ _ => hnn n)
  have h2 := sum_hK K N hK1
  have hK' : (0 : ℝ) < K := by exact_mod_cast hK1
  have h3 : (cnt {n | δ < hK K n} N : ℝ) * δ ≤ N / K := h1.trans h2
  rw [le_div_iff₀ hK'] at h3
  rw [le_div_iff₀ (by positivity)]
  calc (cnt {n | δ < hK K n} N : ℝ) * (K * δ) = cnt {n | δ < hK K n} N * δ * K := by ring
    _ ≤ N := h3


/-! ## Density-zero criteria -/

lemma dens0_of {S : Set ℕ} (h : ∀ ε > 0, ∃ N0 : ℕ, ∀ N ≥ N0, (cnt S N : ℝ) ≤ ε * N) :
    S.HasDensity 0 := by
  rw [hasDensity_iff, Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨N0, hN0⟩ := h (ε / 2) (by positivity)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 := hN0 N (by omega)
  have h0 : (0 : ℝ) ≤ cnt S N := by positivity
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity), div_lt_iff₀ hNpos]
  nlinarith

lemma cnt_le_of_dens0 {S : Set ℕ} (h : S.HasDensity 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ N ≥ N0, (cnt S N : ℝ) ≤ ε * N := by
  rw [hasDensity_iff, Metric.tendsto_atTop] at h
  obtain ⟨N0, hN0⟩ := h ε hε
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 := hN0 N (by omega)
  rw [Real.dist_eq, sub_zero, abs_lt, lt_div_iff₀ hNpos, div_lt_iff₀ hNpos] at h1
  linarith [h1.2]

lemma dens0_union {S T : Set ℕ} (hS : S.HasDensity 0) (hT : T.HasDensity 0) :
    (S ∪ T).HasDensity 0 := by
  refine dens0_of fun ε hε => ?_
  obtain ⟨N1, h1⟩ := cnt_le_of_dens0 hS (half_pos hε)
  obtain ⟨N2, h2⟩ := cnt_le_of_dens0 hT (half_pos hε)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  have := cnt_union_le S T N
  have h1' := h1 N (le_of_max_le_left hN)
  have h2' := h2 N (le_of_max_le_right hN)
  have : (cnt (S ∪ T) N : ℝ) ≤ cnt S N + cnt T N := by exact_mod_cast this
  linarith

lemma dens0_of_sub {S : Set ℕ}
    (h : ∀ ε > 0, ∃ Z : Set ℕ, ∃ d : ℝ, S ⊆ Z ∧ Z.HasDensity d ∧ d ≤ ε) :
    S.HasDensity 0 := by
  refine dens0_of fun ε hε => ?_
  obtain ⟨Z, d, hSZ, hZ, hd⟩ := h (ε / 2) (half_pos hε)
  rw [hasDensity_iff, Metric.tendsto_atTop] at hZ
  obtain ⟨N0, hN0⟩ := hZ (ε / 2) (half_pos hε)
  refine ⟨N0 + 1, fun N hN => ?_⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have h1 := hN0 N (by omega)
  rw [Real.dist_eq, abs_lt] at h1
  have h2 : (cnt Z N : ℝ) / N < ε := by linarith [h1.2]
  rw [div_lt_iff₀ hNpos] at h2
  have h3 : (cnt S N : ℝ) ≤ cnt Z N := by exact_mod_cast cnt_mono hSZ N
  linarith

/-! ## Primes in the progression 1 mod p: divergence -/

lemma log_div_rpow_le {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 1 < x) :
    Real.log n / (n : ℝ) ^ x ≤ (1 / (n : ℝ)) / (x - 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : 0 < x - 1 := by linarith
  have hpow : (n : ℝ) ^ x = n * (n : ℝ) ^ (x - 1) := by
    rw [show x = 1 + (x - 1) by ring, Real.rpow_add hn0, Real.rpow_one]; ring_nf
  have hq : 0 < (n : ℝ) ^ (x - 1) := Real.rpow_pos_of_pos hn0 _
  have hlog : (x - 1) * Real.log n ≤ (n : ℝ) ^ (x - 1) := by
    have := Real.log_le_sub_one_of_pos hq
    rw [Real.log_rpow hn0] at this
    linarith
  rw [hpow, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith

lemma zmod_one_iff (p : ℕ) (hp : 2 ≤ p) (n : ℕ) : ((n : ZMod p) = 1) ↔ n % p = 1 := by
  have : ((1 : ℕ) : ZMod p) = 1 := Nat.cast_one
  rw [← this, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (by omega : 1 < p)]

lemma ap_not_summable (p : ℕ) (hp : p.Prime) :
    ¬ Summable (fun n : ℕ => if n.Prime ∧ n % p = 1 then 1 / (n : ℝ) else 0) := by
  intro hs
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set h : ℕ → ℝ := fun n => if n.Prime ∧ n % p = 1 then 1 / (n : ℝ) else 0 with hh
  have hnn : ∀ n, 0 ≤ h n := fun n => by simp only [hh]; split_ifs <;> positivity
  obtain ⟨C, hC⟩ := ArithmeticFunction.vonMangoldt.LSeries_residueClass_lower_bound
    (q := p) (a := (1 : ZMod p)) isUnit_one
  set A : ℝ := (p.totient : ℝ)⁻¹ with hA
  have hApos : 0 < A := by
    rw [hA]; have : 0 < p.totient := Nat.totient_pos.2 hp.pos
    positivity
  -- choose the tail
  have ht := tendsto_sum_nat_add h
  rw [Metric.tendsto_atTop] at ht
  obtain ⟨X, hX⟩ := ht (A / 2) (half_pos hApos)
  have hXt := hX X le_rfl
  rw [Real.dist_eq, sub_zero] at hXt
  set h' : ℕ → ℝ := fun n => if X ≤ n then h n else 0 with hh'
  have hs' : Summable h' := Summable.of_nonneg_of_le
    (fun n => by simp only [hh']; split_ifs; exacts [hnn n, le_rfl])
    (fun n => by simp only [hh']; split_ifs; exacts [le_rfl, hnn n]) hs
  have htail : ∑' n, h' n ≤ A / 2 := by
    rw [← hs'.sum_add_tsum_nat_add X]
    have e1 : ∑ i ∈ Finset.range X, h' i = 0 :=
      Finset.sum_eq_zero fun i hi => by
        simp only [Finset.mem_range] at hi; simp only [hh']; rw [if_neg (by omega)]
    have e2 : ∑' i, h' (i + X) = ∑' i, h (i + X) :=
      tsum_congr fun i => by simp only [hh']; rw [if_pos (by omega)]
    rw [e1, e2, zero_add]
    exact (le_abs_self _).trans hXt.le
  -- summable pieces
  set r := ArithmeticFunction.vonMangoldt.residueClass (1 : ZMod p) with hr
  have hr0 : ∀ n, 0 ≤ r n := fun n => ArithmeticFunction.vonMangoldt.residueClass_nonneg _ n
  set g1 : ℕ → ℝ := fun n => (if n.Prime then 0 else r n) / n +
    (if n < X then r n else 0) with hg1
  have hg1s : Summable g1 := by
    refine (ArithmeticFunction.vonMangoldt.summable_residueClass_non_primes_div _).add ?_
    refine summable_of_ne_finset_zero (s := Finset.range X) fun n hn => ?_
    simp only [Finset.mem_range] at hn
    rw [if_neg hn]
  have hbound : ∀ {x : ℝ}, 1 < x → ∀ n, r n / (n : ℝ) ^ x ≤ g1 n + h' n / (x - 1) := by
    intro x hx n
    have hx1 : 0 < x - 1 := by linarith
    have hh'0 : 0 ≤ h' n / (x - 1) := by
      have : 0 ≤ h' n := by simp only [hh']; split_ifs; exacts [hnn n, le_rfl]
      positivity
    have hA1 : 0 ≤ (if n.Prime then 0 else r n) / n := by split_ifs <;> positivity [hr0 n]
    have hA2 : 0 ≤ (if n < X then r n else 0) := by split_ifs <;> first | exact hr0 n | exact le_rfl
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have : r 0 = 0 := ArithmeticFunction.vonMangoldt.residueClass_apply_zero _
      rw [this, zero_div]; simp only [hg1]; linarith
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    have hge : (n : ℝ) ≤ (n : ℝ) ^ x := by
      have h1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le h1 hx.le
    have hrx : r n / (n : ℝ) ^ x ≤ r n / n :=
      div_le_div_of_nonneg_left (hr0 n) hn0 hge
    by_cases hpr : n.Prime
    · by_cases hnX : n < X
      · have : r n / (n : ℝ) ^ x ≤ r n := by
          refine div_le_self (hr0 n) ?_
          have : (1 : ℝ) ≤ n := by exact_mod_cast hn
          linarith
        simp only [hg1, if_pos hpr, if_pos hnX, zero_div, zero_add]
        linarith
      · simp only [hg1, if_pos hpr, if_neg hnX, zero_div, add_zero]
        by_cases hm : (n : ZMod p) = 1
        · have hrn : r n = Real.log n := by
            simp only [hr, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply,
              Set.mem_setOf_eq, if_pos hm]
            exact ArithmeticFunction.vonMangoldt_apply_prime hpr
          have hm' : n % p = 1 := (zmod_one_iff p hp.two_le n).1 hm
          have hhn : h' n = 1 / (n : ℝ) := by
            simp only [hh', hh]; rw [if_pos (by omega), if_pos ⟨hpr, hm'⟩]
          rw [hrn, hhn, zero_add]
          exact log_div_rpow_le hn hx
        · have hrn : r n = 0 := by
            simp only [hr, ArithmeticFunction.vonMangoldt.residueClass, Set.indicator_apply,
              Set.mem_setOf_eq, if_neg hm]
          rw [hrn, zero_div, zero_add]; exact hh'0
    · simp only [hg1, if_neg hpr]
      linarith
  -- contradiction
  set G := ∑' n, g1 n with hG
  have key : ∀ {x : ℝ}, 1 < x → x ≤ 2 → A / (x - 1) - C ≤ G + (A / 2) / (x - 1) := by
    intro x hx hx2
    have hx1 : 0 < x - 1 := by linarith
    have hsum : Summable fun n => g1 n + h' n / (x - 1) := hg1s.add (hs'.div_const _)
    have hl : Summable fun n => r n / (n : ℝ) ^ x := Summable.of_nonneg_of_le
      (fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · have : r 0 = 0 := ArithmeticFunction.vonMangoldt.residueClass_apply_zero _
          rw [this, zero_div]
        · have : (0 : ℝ) < (n : ℝ) ^ x := Real.rpow_pos_of_pos (by exact_mod_cast hn) _
          exact div_nonneg (hr0 n) this.le)
      (hbound hx) hsum
    have h1 := hC ⟨hx, hx2⟩
    have h2 : ∑' n, r n / (n : ℝ) ^ x ≤ ∑' n, (g1 n + h' n / (x - 1)) :=
      Summable.tsum_le_tsum (hbound hx) hl hsum
    rw [hg1s.tsum_add (hs'.div_const _)] at h2
    rw [tsum_div_const] at h2
    have h3 : (∑' n, h' n) / (x - 1) ≤ (A / 2) / (x - 1) :=
      div_le_div_of_nonneg_right htail hx1.le
    exact h1.trans (h2.trans (by linarith))
  set t : ℝ := min 1 (A / (2 * (|C + G| + 1))) with ht
  have ht0 : 0 < t := lt_min one_pos (by positivity)
  have ht1 : t ≤ 1 := min_le_left _ _
  have ht2 : t ≤ A / (2 * (|C + G| + 1)) := min_le_right _ _
  have := key (x := 1 + t) (by linarith) (by linarith)
  rw [show 1 + t - 1 = t by ring] at this
  have h4 : A / t - (A / 2) / t ≤ C + G := by linarith
  have h5 : A / t - (A / 2) / t = A / (2 * t) := by field_simp; ring
  rw [h5] at h4
  have h6 : |C + G| + 1 ≤ A / (2 * t) := by
    rw [le_div_iff₀ (by positivity)]
    rw [le_div_iff₀ (by positivity)] at ht2
    linarith
  have := le_abs_self (C + G)
  linarith

lemma ap_diverge (p : ℕ) (hp : p.Prime) (R : ℝ) :
    ∃ L, R ≤ ∑ q ∈ (Finset.range L).filter (fun q => q.Prime ∧ q % p = 1), 1 / (q : ℝ) := by
  by_contra hc
  push_neg at hc
  apply ap_not_summable p hp
  refine summable_of_sum_range_le (c := R) (fun n => ?_) (fun n => ?_)
  · split_ifs <;> positivity
  · rw [← Finset.sum_filter]; exact (hc n).le

/-! ## Sieve: small primes dividing `n` also divide `φ n` -/

lemma prod_le_exp (s : Finset ℕ) :
    ∏ q ∈ s, (1 - 1 / (q : ℝ)) ≤ Real.exp (-∑ q ∈ s, 1 / (q : ℝ)) := by
  rw [← Finset.sum_neg_distrib, Real.exp_sum]
  refine Finset.prod_le_prod (fun q _ => one_sub_nonneg' q) (fun q _ => ?_)
  have := Real.add_one_le_exp (-(1 / (q : ℝ)))
  linarith

lemma Bp_dens0 (p : ℕ) (hp : p.Prime) :
    {n | p ∣ n ∧ ¬ p ∣ Nat.totient n}.HasDensity 0 := by
  refine dens0_of_sub fun ε hε => ?_
  obtain ⟨L, hL⟩ := ap_diverge p hp (1 / ε)
  set Q := (Finset.range L).filter (fun q => q.Prime ∧ q % p = 1) with hQ
  have hQp : ∀ q ∈ Q, q.Prime := fun q hq => (Finset.mem_filter.1 hq).2.1
  refine ⟨{n | status Q n = ∅}, w Q ∅, ?_, density_status Q hQp ∅ (Finset.empty_subset _), ?_⟩
  · rintro n ⟨hpn, hpphi⟩
    simp only [Set.mem_setOf_eq, status, Finset.filter_eq_empty_iff]
    intro q hq hqn
    obtain ⟨_, hqpr, hqp⟩ := Finset.mem_filter.1 hq
    apply hpphi
    have h1 : Nat.totient q ∣ Nat.totient n := Nat.totient_dvd_of_dvd hqn
    rw [Nat.totient_prime hqpr] at h1
    refine dvd_trans ?_ h1
    have := Nat.div_add_mod q p
    exact ⟨q / p, by omega⟩
  · have e : w Q ∅ = ∏ q ∈ Q, (1 - 1 / (q : ℝ)) := by simp [w]
    rw [e]
    refine (prod_le_exp Q).trans ?_
    set s := ∑ q ∈ Q, 1 / (q : ℝ)
    have h1 := Real.add_one_le_exp s
    have hs0 : 0 < 1 / ε := by positivity
    have hpos : 0 < Real.exp s := Real.exp_pos s
    rw [Real.exp_neg, inv_le_comm₀ hpos hε]
    have : 1 / ε ≤ s := hL
    rw [one_div] at this
    linarith

lemma B1_dens0 (Q : Finset ℕ) (hQ : ∀ p ∈ Q, p.Prime) :
    {n | ∃ p ∈ Q, p ∣ n ∧ ¬ p ∣ Nat.totient n}.HasDensity 0 := by
  induction Q using Finset.induction_on with
  | empty => simpa using (show (∅ : Set ℕ).HasDensity 0 from by
      rw [hasDensity_iff]; simp [cnt])
  | insert a Q haQ ih =>
    have e : {n | ∃ p ∈ insert a Q, p ∣ n ∧ ¬ p ∣ Nat.totient n} =
        {n | a ∣ n ∧ ¬ a ∣ Nat.totient n} ∪ {n | ∃ p ∈ Q, p ∣ n ∧ ¬ p ∣ Nat.totient n} := by
      ext n; simp
    rw [e]
    exact dens0_union (Bp_dens0 a (hQ a (Finset.mem_insert_self a Q)))
      (ih fun p hp => hQ p (Finset.mem_insert_of_mem hp))

/-! ## A Wallis-type lower bound for `∏_{p ≤ K} (1 - 1/p)` -/

lemma g_anti {D E : Finset ℕ} (h : D ⊆ E) : g E ≤ g D := by
  unfold g
  rw [← Finset.prod_sdiff h]
  have h1 : ∏ p ∈ E \ D, (1 - 1 / (p : ℝ)) ≤ 1 :=
    Finset.prod_le_one (fun p _ => one_sub_nonneg' p) (fun p _ => by
      have : 0 ≤ 1 / (p : ℝ) := by positivity
      linarith)
  have h2 : 0 ≤ ∏ p ∈ D, (1 - 1 / (p : ℝ)) := Finset.prod_nonneg fun p _ => one_sub_nonneg' p
  nlinarith

lemma g_le_one (D : Finset ℕ) : g D ≤ 1 := by
  have := g_anti (Finset.empty_subset D)
  simpa [g] using this

lemma QK_step (M : ℕ) (hM : 1 ≤ M) :
    g (QK (2 * M + 1)) * (1 - 1 / ((2 * M + 3 : ℕ) : ℝ)) ≤ g (QK (2 * (M + 1) + 1)) := by
  have e : QK (2 * (M + 1) + 1) =
      (if (2 * M + 3).Prime then insert (2 * M + 3) (QK (2 * M + 1)) else QK (2 * M + 1)) := by
    unfold QK
    rw [show 2 * (M + 1) + 1 + 1 = (2 * M + 2 + 1) + 1 by ring, Finset.range_add_one,
      Finset.filter_insert, Finset.range_add_one, Finset.filter_insert]
    have hnp : ¬ (2 * M + 2).Prime := by
      rw [show 2 * M + 2 = 2 * (M + 1) by ring]
      exact Nat.not_prime_mul (by omega) (by omega)
    rw [if_neg hnp, show 2 * M + 2 + 1 = 2 * M + 3 by ring,
      show 2 * M + 1 + 1 = 2 * M + 2 by ring]
  rw [e]
  have hg := g_nonneg (QK (2 * M + 1))
  split_ifs with hpr
  · rw [g_insert (by simp [QK])]
    rw [mul_comm]
  · have : 0 ≤ 1 / ((2 * M + 3 : ℕ) : ℝ) := by positivity
    nlinarith

lemma wallis (M : ℕ) (hM : 1 ≤ M) :
    1 / 4 ≤ g (QK (2 * M + 1)) ^ 2 * ((2 * M + 1 : ℕ) : ℝ) := by
  induction M, hM using Nat.le_induction with
  | base =>
    have : QK (2 * 1 + 1) = {2, 3} := by decide
    rw [this]
    simp [g]
    norm_num
  | succ M hM ih =>
    have hs := QK_step M hM
    have hg := g_nonneg (QK (2 * M + 1))
    set a := g (QK (2 * M + 1))
    set b := g (QK (2 * (M + 1) + 1))
    have hm : (0 : ℝ) < ((2 * M + 3 : ℕ) : ℝ) := by positivity
    have e1 : (1 - 1 / ((2 * M + 3 : ℕ) : ℝ)) = ((2 * M + 2 : ℕ) : ℝ) / ((2 * M + 3 : ℕ) : ℝ) := by
      field_simp; push_cast; ring
    rw [e1] at hs
    have hab : 0 ≤ a * (((2 * M + 2 : ℕ) : ℝ) / ((2 * M + 3 : ℕ) : ℝ)) := by positivity
    have hsq : (a * (((2 * M + 2 : ℕ) : ℝ) / ((2 * M + 3 : ℕ) : ℝ))) ^ 2 ≤ b ^ 2 :=
      pow_le_pow_left₀ hab hs 2
    rw [show 2 * (M + 1) + 1 = 2 * M + 3 by ring]
    have key : a ^ 2 * ((2 * M + 1 : ℕ) : ℝ) ≤
        (a * (((2 * M + 2 : ℕ) : ℝ) / ((2 * M + 3 : ℕ) : ℝ))) ^ 2 * ((2 * M + 3 : ℕ) : ℝ) := by
      have : ((2 * M + 1 : ℕ) : ℝ) ≤ ((2 * M + 2 : ℕ) : ℝ) ^ 2 / ((2 * M + 3 : ℕ) : ℝ) := by
        rw [le_div_iff₀ hm]; push_cast; nlinarith
      have h0 : 0 ≤ a ^ 2 := sq_nonneg a
      have e2 : (a * (((2 * M + 2 : ℕ) : ℝ) / ((2 * M + 3 : ℕ) : ℝ))) ^ 2 *
          ((2 * M + 3 : ℕ) : ℝ) = a ^ 2 * (((2 * M + 2 : ℕ) : ℝ) ^ 2 / ((2 * M + 3 : ℕ) : ℝ)) := by
        field_simp
      rw [e2]
      exact mul_le_mul_of_nonneg_left this h0
    nlinarith

/-! ## The pointwise inequality -/

lemma pointwise (K n F : ℕ) (hn : 2 ≤ n) (h1 : ∀ p ∈ QK K, p ∣ n → p ∣ Nat.totient n)
    (h2 : hK K n ≤ g (QK K) / 4) (h3 : (F : ℝ) < n * g (QK K) ^ 2 / 2) :
    Nat.totient (n - Nat.totient n) + F < Nat.totient n := by
  have hn0 : n ≠ 0 := by omega
  set c := g (QK K) with hc
  set P := g (status (QK K) n) with hP
  have hsub : status (QK K) n ⊆ QK K := Finset.filter_subset _ _
  have hcP : c ≤ P := g_anti hsub
  have hc0 : 0 ≤ c := g_nonneg _
  have hP1 : P ≤ 1 := g_le_one _
  set Λ := ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ≤ K), (1 - 1 / (p : ℝ)) with hΛ
  have hΛ1 : 1 - hK K n ≤ Λ := prod_ge _
  have hphi : (Nat.totient n : ℝ) = n * (P * Λ) := phi_split hn0 K
  have hlt : Nat.totient n < n := Nat.totient_lt n (by omega)
  set m := n - Nat.totient n with hm
  have hm0 : m ≠ 0 := by omega
  have hmR : (m : ℝ) = n - Nat.totient n := by
    rw [hm, Nat.cast_sub hlt.le]
  have hphim : (Nat.totient m : ℝ) ≤ m * P := by
    rw [phi_eq hm0]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have hs : status (QK K) n ⊆ m.primeFactors := by
      intro p hp
      obtain ⟨hpQ, hpn⟩ := Finset.mem_filter.1 hp
      rw [Nat.mem_primeFactors]
      exact ⟨QK_prime K p hpQ, Nat.dvd_sub hpn (h1 p hpQ hpn), hm0⟩
    exact g_anti hs
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hF : (F : ℝ) < n * P ^ 2 / 2 := by
    have : c ^ 2 ≤ P ^ 2 := pow_le_pow_left₀ hc0 hcP 2
    nlinarith
  have hP0 : 0 ≤ P := hc0.trans hcP
  have hΛ' : 1 - P / 4 ≤ Λ := by linarith
  -- (n - nPΛ) P + n P^2/2 ≤ n P Λ
  have hkey : (n - n * (P * Λ)) * P + n * P ^ 2 / 2 ≤ n * (P * Λ) := by
    have h4 : 1 + P / 2 ≤ Λ * (1 + P) := by nlinarith
    have h5 : 0 ≤ (n : ℝ) * P := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h4 h5]
  have : (Nat.totient m : ℝ) + F < Nat.totient n := by
    rw [hmR, hphi] at *
    calc (Nat.totient m : ℝ) + F < (n - n * (P * Λ)) * P + n * P ^ 2 / 2 := by
          have := hphim; rw [hmR, hphi] at this; linarith
      _ ≤ n * (P * Λ) := hkey
  exact_mod_cast this

/-! ## Assembly -/

lemma cnt_Iio_le (n0 N : ℕ) : cnt (Set.Iio n0) N ≤ n0 := by
  unfold cnt
  refine (Finset.card_le_card ?_).trans (Finset.card_range n0).le
  intro x hx
  simp only [Finset.mem_filter, Set.mem_Iio] at hx; simpa using hx.2

lemma choose_K (ε : ℝ) (hε : 0 < ε) :
    ∃ K : ℕ, 1 ≤ K ∧ 0 < g (QK K) ∧ 12 / ε ≤ K * g (QK K) := by
  obtain ⟨M, hM⟩ := exists_nat_gt (4 * (12 / ε) ^ 2)
  refine ⟨2 * (M + 1) + 1, by omega, ?_, ?_⟩
  · have h := wallis (M + 1) (by omega)
    have hg := g_nonneg (QK (2 * (M + 1) + 1))
    rcases hg.lt_or_eq with h' | h'
    · exact h'
    · rw [← h'] at h; norm_num at h
  · have h := wallis (M + 1) (by omega)
    have hg := g_nonneg (QK (2 * (M + 1) + 1))
    set c := g (QK (2 * (M + 1) + 1))
    set Kr : ℝ := ((2 * (M + 1) + 1 : ℕ) : ℝ)
    have hK : 4 * (12 / ε) ^ 2 ≤ Kr := by
      simp only [Kr]; push_cast
      have : (M : ℝ) ≤ 2 * (M + 1) + 1 := by linarith
      linarith
    have hKpos : 0 ≤ Kr := by positivity
    have hsq : (12 / ε) ^ 2 ≤ (Kr * c) ^ 2 := by nlinarith
    have hx : 0 ≤ Kr * c := by positivity
    have h12 : 0 ≤ 12 / ε := by positivity
    nlinarith

lemma compl_dens0 (f : ℕ → ℕ) (hf : (fun n ↦ (f n : ℝ)) =o[atTop] (fun n ↦ (n : ℝ))) :
    {n : ℕ | Nat.totient (n - Nat.totient n) + f n < Nat.totient n}ᶜ.HasDensity 0 := by
  refine dens0_of fun ε hε => ?_
  obtain ⟨K, hK1, hc, hKc⟩ := choose_K ε hε
  set c := g (QK K) with hcdef
  -- small n
  have hfo := hf.def (show 0 < c ^ 2 / 4 by positivity)
  rw [eventually_atTop] at hfo
  obtain ⟨n1, hn1⟩ := hfo
  set n0 := max n1 2
  -- B1
  obtain ⟨N1, hN1⟩ := cnt_le_of_dens0 (B1_dens0 (QK K) (QK_prime K)) (show 0 < ε / 3 by positivity)
  obtain ⟨N2, hN2⟩ := exists_nat_gt (3 * n0 / ε)
  refine ⟨max N1 N2, fun N hN => ?_⟩
  set B1 := {n | ∃ p ∈ QK K, p ∣ n ∧ ¬ p ∣ Nat.totient n}
  set B2 := {n | c / 4 < hK K n}
  have hsub : {n : ℕ | Nat.totient (n - Nat.totient n) + f n < Nat.totient n}ᶜ ⊆
      (Set.Iio n0 ∪ B1) ∪ B2 := by
    intro n hn
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq] at hn
    by_contra hc'
    simp only [Set.mem_union, Set.mem_Iio, not_or, B1, B2, Set.mem_setOf_eq, not_lt,
      not_exists, not_and, not_not] at hc'
    obtain ⟨⟨h0, hb1⟩, hb2⟩ := hc'
    apply hn
    refine pointwise K n (f n) (le_of_max_le_right h0) (fun p hp hpn => hb1 p hp hpn) hb2 ?_
    have h5 := hn1 n (le_of_max_le_left h0)
    rw [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity)] at h5
    have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
    have : 0 < c ^ 2 * n := by positivity
    have : c ^ 2 / 4 * n < n * c ^ 2 / 2 := by linarith
    linarith
  have hcnt := cnt_mono hsub N
  have hu1 := cnt_union_le (Set.Iio n0 ∪ B1) B2 N
  have hu2 := cnt_union_le (Set.Iio n0) B1 N
  have hI := cnt_Iio_le n0 N
  have hB1 := hN1 N (le_of_max_le_left hN)
  have hB2 := cnt_bad K N hK1 (show 0 < c / 4 by positivity)
  have hNpos : (0 : ℝ) < N := by
    have : (0 : ℝ) ≤ 3 * n0 / ε := by positivity
    have h' : (N2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
    linarith
  have hB2' : (N : ℝ) / (K * (c / 4)) ≤ ε / 3 * N := by
    rw [div_le_iff₀ (by positivity)]
    have hKr : (0 : ℝ) < K := by exact_mod_cast hK1
    have : 12 ≤ ε * (K * c) := by rwa [div_le_iff₀ hε, mul_comm] at hKc
    nlinarith
  have hI' : (n0 : ℝ) ≤ ε / 3 * N := by
    have h' : (N2 : ℝ) ≤ N := by exact_mod_cast le_of_max_le_right hN
    have : 3 * n0 / ε < N := lt_of_lt_of_le hN2 h'
    rw [div_lt_iff₀ hε] at this
    linarith
  have e : (cnt {n : ℕ | Nat.totient (n - Nat.totient n) + f n < Nat.totient n}ᶜ N : ℝ) ≤
      cnt (Set.Iio n0) N + cnt B1 N + cnt B2 N := by
    exact_mod_cast hcnt.trans (hu1.trans (Nat.add_le_add_right hu2 _))
  have hI'' : (cnt (Set.Iio n0) N : ℝ) ≤ n0 := by exact_mod_cast hI
  linarith

end OMA1064

theorem OMA.solution : type_of% @Erdos1064.erdos_1064 := by
  have h0 := OMA1064.compl_dens0 (fun _ => 0)
    (by simpa using Asymptotics.isLittleO_zero (fun n : ℕ => (n : ℝ)) atTop)
  have hu : (Set.univ : Set ℕ).HasDensity 1 := by simp
  have := OMA1064.HasDensity.diff hu (by simpa using h0)
  simpa [gt_iff_lt] using this
