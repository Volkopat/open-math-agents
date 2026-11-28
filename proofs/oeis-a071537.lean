import OMAStatements.S_oeis_a071537

-- Credit: @bnb9001; proof drafted by Codex (GPT-6 Astra).
open scoped BigOperators
namespace CodexA071537
open OMA.S_oeis_a071537
noncomputable def num (n : ℕ) : ℚˣ := Units.mk0 (max n 1 : ℕ) (by positivity)
noncomputable def ev : (ℕ →₀ ℤ) →ₗ[ℤ] Additive ℚˣ :=
  Finsupp.linearCombination ℤ (fun n => Additive.ofMul (num n))

def Supported (c : ℕ →₀ ℤ) (n m : ℕ) : Prop :=
  ∀ i, c i ≠ 0 → n ≤ i ∧ i ≤ m

def Rel (n m : ℕ) : Prop :=
  ∃ c : ℕ →₀ ℤ, Supported c n m ∧ c n ≠ 0 ∧ ev c = 0

noncomputable def seq (n : ℕ) : ℕ := sInf {m | Rel n m}

@[simp] lemma ev_single (n : ℕ) (z : ℤ) :
    ev (Finsupp.single n z) = z • Additive.ofMul (num n) := by
  simp [ev]

@[simp] lemma num_one : num 1 = 1 := by
  apply Units.ext
  norm_num [num]

lemma num_mul {a b : ℕ} (ha : 0 < a) (hb : 0 < b) : num (a*b) = num a * num b := by
  apply Units.ext
  simp [num, max_eq_left (by omega : 1 ≤ a), max_eq_left (by omega : 1 ≤ b),
    max_eq_left (by nlinarith : 1 ≤ a*b)]

lemma supported_single (n m i : ℕ) (z : ℤ) (hni : n ≤ i) (him : i ≤ m) :
    Supported (Finsupp.single i z) n m := by
  intro j hj
  by_cases hij : i = j
  · subst j; exact ⟨hni, him⟩
  · simp [hij] at hj

lemma Supported.add {c d : ℕ →₀ ℤ} {n m : ℕ}
    (hc : Supported c n m) (hd : Supported d n m) : Supported (c+d) n m := by
  intro i hi
  by_cases hci : c i = 0
  · exact hd i (by simpa [hci] using hi)
  · exact hc i hci

lemma Supported.sub {c d : ℕ →₀ ℤ} {n m : ℕ}
    (hc : Supported c n m) (hd : Supported d n m) : Supported (c-d) n m := by
  intro i hi
  by_cases hci : c i = 0
  · exact hd i (by simpa [hci] using hi)
  · exact hc i hci

lemma Supported.smul {c : ℕ →₀ ℤ} {n m : ℕ} (hc : Supported c n m) (z : ℤ) :
    Supported (z • c) n m := by
  intro i hi
  exact hc i (by intro h; simp [h] at hi)

lemma Supported.mono {c : ℕ →₀ ℤ} {n m n' m' : ℕ} (hc : Supported c n m)
    (hn : n' ≤ n) (hm : m ≤ m') : Supported c n' m' := by
  intro i hi
  obtain ⟨h1,h2⟩ := hc i hi
  exact ⟨hn.trans h1, h2.trans hm⟩

lemma Supported.zero_below {c : ℕ →₀ ℤ} {n m i : ℕ} (hc : Supported c n m)
    (hi : i < n) : c i = 0 := by
  by_contra h
  have := (hc i h).1
  omega

lemma Supported.zero_above {c : ℕ →₀ ℤ} {n m i : ℕ} (hc : Supported c n m)
    (hi : m < i) : c i = 0 := by
  by_contra h
  have := (hc i h).2
  omega

lemma rel_one : Rel 1 1 := by
  refine ⟨Finsupp.single 1 1, supported_single _ _ _ _ le_rfl le_rfl, by simp, ?_⟩
  simp

lemma exists_rel {n : ℕ} (hn : 0 < n) : ∃ m, Rel n m := by
  by_cases hn1 : n = 1
  · subst n; exact ⟨1, rel_one⟩
  have hn2 : 2 ≤ n := by omega
  have hnn : n < n*(n+1) := by nlinarith
  have hsucc : n+1 < n*(n+1) := by nlinarith
  refine ⟨n*(n+1), Finsupp.single n 1 + Finsupp.single (n+1) 1 -
    Finsupp.single (n*(n+1)) 1, ?_, ?_, ?_⟩
  · exact ((supported_single _ _ _ _ le_rfl hnn.le).add
      (supported_single _ _ _ _ (by omega) hsucc.le)).sub
      (supported_single _ _ _ _ hnn.le le_rfl)
  · simp [ne_of_lt hnn]
  · simp only [map_sub, map_add, ev_single, one_smul]
    apply sub_eq_zero.mpr
    change Additive.ofMul (num n * num (n+1)) = Additive.ofMul (num (n*(n+1)))
    rw [num_mul hn (by omega)]

lemma seq_rel {n : ℕ} (hn : 0 < n) : Rel n (seq n) :=
  Nat.sInf_mem (exists_rel hn)

lemma seq_le {n m : ℕ} (h : Rel n m) : seq n ≤ m := Nat.sInf_le h

lemma le_seq {n : ℕ} (hn : 0 < n) : n ≤ seq n := by
  obtain ⟨c, hc, hcn, _⟩ := seq_rel hn
  exact (hc n hcn).2

lemma last_ne_zero {n : ℕ} (hn : 0 < n) {c : ℕ →₀ ℤ}
    (hc : Supported c n (seq n)) (hcn : c n ≠ 0) (he : ev c = 0) :
    c (seq n) ≠ 0 := by
  intro hz
  have hm : 0 < seq n := lt_of_lt_of_le hn (le_seq hn)
  have hr : Rel n (seq n-1) := by
    refine ⟨c, ?_, hcn, he⟩
    intro i hi
    obtain ⟨h1,h2⟩ := hc i hi
    have hne : i ≠ seq n := by intro h; subst i; exact hi hz
    exact ⟨h1, by omega⟩
  have := seq_le hr
  omega

lemma seq_ne_of_lt {n r : ℕ} (hn : 0 < n) (hnr : n < r) : seq n ≠ seq r := by
  intro heq
  have hr : 0 < r := by omega
  obtain ⟨c, hc, hcn, hce⟩ := seq_rel hn
  obtain ⟨d, hd, hdr, hde⟩ := seq_rel hr
  have hdm : d (seq r) ≠ 0 := last_ne_zero hr hd hdr hde
  have hdn : d n = 0 := hd.zero_below hnr
  let e : ℕ →₀ ℤ := d (seq r) • c - c (seq n) • d
  have hen : e n ≠ 0 := by
    simp [e, hdn, mul_ne_zero hdm hcn]
  have hem : e (seq n) = 0 := by simp [e, heq, mul_comm]
  have hee : ev e = 0 := by simp [e, hce, hde]
  have hs : Supported e n (seq n) :=
    (hc.smul _).sub ((hd.mono hnr.le (by omega)).smul _)
  have hrel : Rel n (seq n-1) := by
    refine ⟨e, ?_, hen, hee⟩
    intro i hi
    obtain ⟨h1,h2⟩ := hs i hi
    have hne : i ≠ seq n := by intro h; subst i; exact hi hem
    exact ⟨h1, by omega⟩
  have := seq_le hrel
  have := le_seq hn
  omega

lemma seq_inj {n r : ℕ} (hn : 0 < n) (hr : 0 < r) (h : seq n = seq r) : n = r := by
  rcases lt_trichotomy n r with hnr | hnr | hnr
  · exact False.elim (seq_ne_of_lt hn hnr h)
  · exact hnr
  · exact False.elim (seq_ne_of_lt hr hnr h.symm)

noncomputable def valuation (p : ℕ) [Fact p.Prime] : Additive ℚˣ →ₗ[ℤ] ℤ where
  toFun x := padicValRat p (x.toMul : ℚ)
  map_add' x y := by
    change padicValRat p ((x.toMul : ℚ) * (y.toMul : ℚ)) = _
    exact padicValRat.mul (Units.ne_zero _) (Units.ne_zero _)
  map_smul' z x := by
    change padicValRat p ((x.toMul ^ z : ℚˣ) : ℚ) = z * _
    simp

lemma valuation_num (p i : ℕ) [Fact p.Prime] (hi : 0 < i) :
    valuation p (Additive.ofMul (num i)) = (padicValNat p i : ℤ) := by
  simp [valuation, num, max_eq_left (by omega : 1 ≤ i)]

lemma last_not_prime {n : ℕ} (hn : 0 < n) : ¬ (seq n).Prime := by
  intro hp
  let : Fact (seq n).Prime := ⟨hp⟩
  obtain ⟨c, hc, hcn, he⟩ := seq_rel hn
  have hcm := last_ne_zero hn hc hcn he
  have hz := congrArg (valuation (seq n)) he
  rw [map_zero] at hz
  change valuation (seq n) (c.sum (fun i z => z • Additive.ofMul (num i))) = 0 at hz
  simp only [Finsupp.sum, map_sum, map_smul] at hz
  have hs : (∑ i ∈ c.support, c i * valuation (seq n) (Additive.ofMul (num i))) = c (seq n) := by
    rw [Finset.sum_eq_single (seq n)]
    · rw [valuation_num _ _ (by have := le_seq hn; omega), padicValNat.self hp.one_lt]
      simp
    · intro i hi him
      obtain ⟨hni, himle⟩ := hc i (Finsupp.mem_support_iff.mp hi)
      rw [valuation_num _ _ (by omega), padicValNat.eq_zero_of_not_dvd]
      · simp
      · exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
    · intro h
      exact False.elim (h (Finsupp.mem_support_iff.mpr hcm))
  exact hcm (hs.symm.trans hz)

def Tail (n m : ℕ) : Prop :=
  ∃ c : ℕ →₀ ℤ, Supported c n m ∧ c n ≠ 0 ∧ c m ≠ 0 ∧ ev c = 0

lemma trim_left {n m : ℕ} {c : ℕ →₀ ℤ} (hc : Supported c n m)
    (hcm : c m ≠ 0) (he : ev c = 0) : ∃ b, n ≤ b ∧ b ≤ m ∧ Tail b m := by
  classical
  have hne : c.support.Nonempty := ⟨m, Finsupp.mem_support_iff.mpr hcm⟩
  let b := c.support.min' hne
  have hbmem : b ∈ c.support := Finset.min'_mem _ _
  have hcb : c b ≠ 0 := Finsupp.mem_support_iff.mp hbmem
  obtain ⟨hnb,hbm⟩ := hc b hcb
  refine ⟨b,hnb,hbm,c,?_,hcb,hcm,he⟩
  intro i hi
  exact ⟨Finset.min'_le _ _ (Finsupp.mem_support_iff.mpr hi), (hc i hi).2⟩

lemma nonprime_tail {s : ℕ} (hs : 0 < s) (hp : ¬ s.Prime) :
    ∃ n, 0 < n ∧ n ≤ s ∧ Tail n s := by
  by_cases hs1 : s = 1
  · subst s
    refine ⟨1, by omega, le_rfl, Finsupp.single 1 1,
      supported_single _ _ _ _ le_rfl le_rfl, by simp, by simp, ?_⟩
    simp
  obtain ⟨a,b,has,hbs,hab⟩ := (Nat.not_prime_iff_exists_mul_eq (by omega : 2 ≤ s)).mp hp
  have ha : 0 < a := by nlinarith
  have hb : 0 < b := by nlinarith
  let c : ℕ →₀ ℤ := Finsupp.single s 1 - (Finsupp.single a 1 + Finsupp.single b 1)
  have hc : Supported c 1 s :=
    (supported_single _ _ _ _ hs le_rfl).sub
      ((supported_single _ _ _ _ ha has.le).add (supported_single _ _ _ _ hb hbs.le))
  have hcs : c s ≠ 0 := by simp [c, ne_of_lt has, ne_of_lt hbs]
  have he : ev c = 0 := by
    simp only [c, map_sub, map_add, ev_single, one_smul]
    apply sub_eq_zero.mpr
    change Additive.ofMul (num s) = Additive.ofMul (num a * num b)
    rw [← hab, num_mul ha hb]
  obtain ⟨n,hn,hns,ht⟩ := trim_left hc hcs he
  exact ⟨n,hn,hns,ht⟩

lemma seq_surj {s : ℕ} (hs : 0 < s) (hp : ¬ s.Prime) : ∃ n, 0 < n ∧ seq n = s := by
  classical
  obtain ⟨a,ha,has,hta⟩ := nonprime_tail hs hp
  let P : ℕ → Prop := fun n => 0 < n ∧ Tail n s
  let n := Nat.findGreatest P s
  have hnP : P n := Nat.findGreatest_spec has ⟨ha,hta⟩
  obtain ⟨hn,c,hc,hcn,hcs,hce⟩ := hnP
  have hle : seq n ≤ s := seq_le ⟨c,hc,hcn,hce⟩
  refine ⟨n,hn,?_⟩
  by_contra hne
  have hlt : seq n < s := by omega
  obtain ⟨d,hd,hdn,hde⟩ := seq_rel hn
  have hds : d s = 0 := hd.zero_above hlt
  let e : ℕ →₀ ℤ := d n • c - c n • d
  have hen : e n = 0 := by simp [e, mul_comm]
  have hes : e s ≠ 0 := by simp [e, hds, mul_ne_zero hdn hcs]
  have hee : ev e = 0 := by simp [e, hce, hde]
  have he0 : Supported e n s := (hc.smul _).sub ((hd.mono le_rfl hle).smul _)
  have he1 : Supported e (n+1) s := by
    intro i hi
    obtain ⟨h1,h2⟩ := he0 i hi
    have hin : i ≠ n := by intro h; subst i; exact hi hen
    exact ⟨by omega,h2⟩
  obtain ⟨b,hnb,hbs,htb⟩ := trim_left he1 hes hee
  exact (Nat.findGreatest_is_greatest (show n < b by omega) hbs) ⟨by omega,htb⟩

theorem auxiliary_bijection :
    Set.BijOn seq {n | 0 < n} {s | 0 < s ∧ ¬ s.Prime} := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact ⟨lt_of_lt_of_le hn (le_seq hn), last_not_prime hn⟩
  · intro n hn r hr h
    exact seq_inj hn hr h
  · intro s hs
    obtain ⟨n, hn, he⟩ := seq_surj hs.1 hs.2
    exact ⟨n,hn,he⟩


lemma ev_product {n m : ℕ} (hn : 0 < n) {c : ℕ →₀ ℤ} (hc : Supported c n m) :
    ((ev c).toMul : ℚ) = ∏ i ∈ Finset.Icc n m, (i : ℚ) ^ c i := by
  have hsub : c.support ⊆ Finset.Icc n m := by
    intro i hi
    exact Finset.mem_Icc.mpr (hc i (Finsupp.mem_support_iff.mp hi))
  change ((c.sum (fun i z => z • Additive.ofMul (num i))).toMul : ℚ) = _
  rw [Finsupp.sum_of_support_subset c hsub _ (by simp)]
  simp only [toMul_sum, toMul_zsmul]
  change (Units.coeHom ℚ) (∏ i ∈ Finset.Icc n m, num i ^ c i) = _
  rw [map_prod]
  simp only [Units.coeHom_apply, Units.val_zpow_eq_zpow_val]
  apply Finset.prod_congr rfl
  intro i hi
  have hni := (Finset.mem_Icc.mp hi).1
  simp [num, max_eq_left (by omega : 1 ≤ i)]

lemma ev_zero_iff_product {n m : ℕ} (hn : 0 < n) {c : ℕ →₀ ℤ}
    (hc : Supported c n m) : ev c = 0 ↔ ∏ i ∈ Finset.Icc n m, (i : ℚ) ^ c i = 1 := by
  rw [← ev_product hn hc]
  constructor
  · intro h; rw [h]; rfl
  · intro h
    have hu : (ev c).toMul = 1 := Units.ext h
    exact congrArg Additive.ofMul hu

lemma rel_iff_productRelation {n m : ℕ} (hn : 0 < n) : Rel n m ↔ ProductRelation n m := by
  classical
  constructor
  · rintro ⟨c,hc,hcn,he⟩
    exact ⟨(hc n hcn).2,c,hcn,(ev_zero_iff_product hn hc).mp he⟩
  · rintro ⟨hnm,k,hkn,hprod⟩
    let f : ℕ → ℤ := fun i => if i ∈ Finset.Icc n m then k i else 0
    have hf : ∀ i, f i ≠ 0 → i ∈ Finset.Icc n m := by
      intro i hi
      by_contra h
      exact hi (if_neg h)
    let c : ℕ →₀ ℤ := Finsupp.onFinset (Finset.Icc n m) f hf
    have hc : Supported c n m := by
      intro i hi
      exact Finset.mem_Icc.mp (hf i hi)
    have hcn : c n ≠ 0 := by simpa [c, f, hnm] using hkn
    refine ⟨c,hc,hcn,(ev_zero_iff_product hn hc).mpr ?_⟩
    calc
      ∏ i ∈ Finset.Icc n m, (i : ℚ) ^ c i = ∏ i ∈ Finset.Icc n m, (i : ℚ) ^ k i := by
        apply Finset.prod_congr rfl
        intro i hi
        change (i : ℚ) ^ (if i ∈ Finset.Icc n m then k i else 0) = _
        rw [if_pos hi]
      _ = 1 := hprod

lemma a_eq_seq {n : ℕ} (hn : 0 < n) : a n = seq n := by
  unfold a seq
  congr 1
  ext m
  exact (rel_iff_productRelation hn).symm

theorem main : Set.BijOn a {n | 0 < n} {s | 0 < s ∧ ¬ s.Prime} := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [a_eq_seq hn]
    exact auxiliary_bijection.mapsTo hn
  · intro n hn r hr h
    rw [a_eq_seq hn, a_eq_seq hr] at h
    exact seq_inj hn hr h
  · intro s hs
    obtain ⟨n,hn,he⟩ := seq_surj hs.1 hs.2
    exact ⟨n,hn,(a_eq_seq hn).trans he⟩


end CodexA071537

theorem OMA.solution : type_of% @OMA.S_oeis_a071537.main := CodexA071537.main
