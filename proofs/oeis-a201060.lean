import OMAStatements.S_oeis_a201060
import Mathlib

namespace OMA.A201060Port

open OMA.S_oeis_a201060

/-!
# A201060 - repdigits a produit de chiffres repdigit

Verbatim OEIS : « Repdigit numbers with repdigit digital product. »
(offset 1,3 ; mots-cles nonn,base.)

Donnees : 0,1,2,3,4,5,6,7,8,9,11,22,33,111,222,1111,11111,111111,...
Les seuls termes non repunits publies sont 22,33,222 (produits
4,9,8 - repdigits a un chiffre) ; 11 et 111 sont des repunits
(produit 1) ; ensuite `a(16) = 1111` et tous les termes connus sont
des repunits (produit 1).

Commentaire OEIS (conjecture de Jaroslav Krizek, 2011) : « a(n) is
repunit060 for n >= 16 » - OUVERTE (affichage OEIS, aucune preuve
referencee). Reduction naturelle : un repdigit positif est
`c * repunit060 m` (`c` dans `1..9`, `m >= 1`) et son produit de chiffres
vaut `c ^ m` ; la conjecture equivaut a « `c ^ m` n'est jamais repdigit
pour `c >= 2`, `m >= 4` » (les exceptions `m <= 3` : `1^2=1`, `2^2=4`,
`3^2=9`, `1^3=1`, `2^3=8` rendent compte des cinq termes 11,22,33,111,222
- repunits pour `c = 1`, non-repunits pour `c >= 2`).

Contenu :
- `IsRepdigit n` : tous les chiffres decimaux de `n` sont egaux
  (`Nat.digits 10` ; pour `n = 0` la liste est vide et `0` est repdigit
  de plein droit - le premier terme OEIS est bien `0`) ;
- `digitProd n` : produit des chiffres (`1` pour `n = 0`, produit vide,
  et `1` est repdigit donc `0` satisfait le predicat de la suite) ;
- `InSeq n` : le predicat exact du verbatim ;
- `repunit060 m = ofDigits 10 (replicate m 1)` (`m` fois le chiffre `1`) :
  `repunit060_eq : repunit060 m = (10 ^ m - 1) / 9`, stricte monotonie ;
- `isRepdigit_iff` : classification « `n` repdigit ssi
  `n = c * repunit060 m` avec `c <= 9`, `m >= 1` » ;
- `digitProd_mul_repunit` : le produit vaut `c ^ m` ;
- `inSeq_mul_repunit` : `InSeq (c * repunit060 m) ssi IsRepdigit (c ^ m)`
  (la reduction de Krizek) ; `inSeq_repunit` (famille infinie) ;
- `a201060 n = Nat.nth InSeq (n - 1)` : le n-ieme terme (offset 1 ;
  `a201060 0` est une valeur de rebut hors domaine) ;
- `inSeq_infinite` (les repunits suffisent), `a201060_mem`,
  `a201060_strictMono`, bornes `n - 1 <= a(n) <= repunit060 n` ;
- classification complete en dessous de `11111` (`seqBelow`) :
  exactement {0..9, 11, 22, 33, 111, 222, 1111} ;
- ancres certifiees `a(1)..a(17)` conformes aux donnees OEIS, dont
  `a(16) = 1111` (premier repunit060) et `a(17) = 11111` ;
- `KrizekConjecture` : l'enonce OEIS ouvert de J. Krizek, ici PROUVE
  (`theorem A201060`) par certificat fini elementaire : tout terme
  `>= 1111` de la suite est un repunit060 - pour `c` dans `2..9`,
  `R_k | c^m` est impossible des `k >= 2` (coprimalite pour `c` pair
  ou `5`, structure 3-adique via `111 = 3 * 37`, structure 7-adique
  via la periode 6 de `R_k mod 7` et `R_2 = 11`). Aucune borne
  limitante : le theoreme est universel en `n`.

Certificats : les comptages `Nat.count InSeq v` ne scannent PAS le
segment `[0, v)` (l'evaluation kernel de `Nat.digits` y serait trop
couteuse) : le lemme structurel `isRepdigit_iff` reduit les candidats
a `c * repunit060 m` (`c <= 9`, `m <= 4`), puis la verification se fait
cas par cas - toute la machinerie est kernel-pure.

Historique : la preuve vivait dans `Check_atk_A201060.lean`
(run 43115106721, LEAN_EXIT=0) ; elle est fusionnee ici (section
`AtkA201060`). La forme fermee `a(n) = repunit060 (n - 12)` pour
`n >= 16` n'est PAS prouvee (non requise par l'enonce OEIS, derivable
par comptage) ; les ancres `a(18)..a(31)` restent une extension
mecanique des memes certificats, sans contenu nouveau.
-/


/-- `IsRepdigit` est decidable (quantificateurs bornes sur une liste). -/
instance : DecidablePred IsRepdigit := fun n => by
  unfold IsRepdigit
  infer_instance



/-- `InSeq` est decidable. -/
instance : DecidablePred InSeq := fun n => by
  unfold InSeq
  infer_instance


/-- `repunit060 0 = 0`. -/
theorem repunit060_zero : repunit060 0 = 0 := rfl

/-- Recurrence : `repunit060 (m+1) = 1 + 10 * repunit060 m`. -/
theorem repunit060_succ (m : ℕ) : repunit060 (m + 1) = 1 + 10 * repunit060 m := by
  unfold repunit060
  rw [List.replicate_succ, Nat.ofDigits_cons]

/-- `repunit060` est strictement croissante. -/
theorem repunit060_strictMono : StrictMono repunit060 := by
  apply strictMono_nat_of_lt_succ
  intro m
  rw [repunit060_succ]
  omega

/-- `repunit060 m >= 1` des que `m >= 1`. -/
theorem repunit060_pos {m : ℕ} (hm : 1 ≤ m) : 1 ≤ repunit060 m := by
  have h := repunit060_strictMono.monotone hm
  have h1 : repunit060 1 = 1 := rfl
  omega

/-- Forme fermee multipliee : `9 * repunit060 m + 1 = 10 ^ m`. -/
theorem repunit060_mul9 (m : ℕ) : repunit060 m * 9 + 1 = 10 ^ m := by
  induction m with
  | zero => rfl
  | succ k ih =>
    rw [repunit060_succ]
    have e : (1 + 10 * repunit060 k) * 9 + 1 = 10 * (repunit060 k * 9 + 1) := by
      ring
    rw [e, ih]
    exact (pow_succ' 10 k).symm

/-- Forme fermee : `repunit060 m = (10 ^ m - 1) / 9`. -/
theorem repunit060_eq (m : ℕ) : repunit060 m = (10 ^ m - 1) / 9 := by
  have h := repunit060_mul9 m
  have e : repunit060 m * 9 = 10 ^ m - 1 := by omega
  rw [← e]
  exact (Nat.mul_div_cancel _ (by norm_num)).symm

/-- Tous les chiffres egaux ssi la liste est un `replicate`. -/
theorem isRepdigit_iff_replicate {n : ℕ} :
    IsRepdigit n ↔ ∃ c : ℕ,
      Nat.digits 10 n = List.replicate (Nat.digits 10 n).length c := by
  constructor
  · intro h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by simp [Nat.digits_zero]⟩
    · have hne : Nat.digits 10 n ≠ [] :=
        Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
      obtain ⟨c, hc⟩ := List.exists_mem_of_ne_nil _ hne
      refine ⟨c, List.eq_replicate_length.mpr ?_⟩
      intro b hb
      exact h b hb c hc
  · rintro ⟨c, hc⟩
    intro d hd e he
    rw [hc, List.mem_replicate] at hd he
    rw [hd.2, he.2]

/-- Tout `n < 10` est repdigit (liste vide ou singleton). -/
theorem isRepdigit_of_lt_ten {n : ℕ} (hn : n < 10) : IsRepdigit n := by
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · intro d hd
    simp [Nat.digits_zero] at hd
  · intro d hd e he
    rw [Nat.digits_of_lt 10 n (by omega) hn, List.mem_singleton] at hd he
    rw [hd, he]

/-- `ofDigits` est lineaire en les chiffres : multiplier chaque
    chiffre par `c` multiplie la valeur par `c`. -/
theorem ofDigits_map_mul (L : List ℕ) (c : ℕ) :
    Nat.ofDigits 10 (L.map (· * c)) = c * Nat.ofDigits 10 L := by
  induction L with
  | nil => simp
  | cons a t ih =>
    simp only [List.map_cons, Nat.ofDigits_cons, ih]
    ring

/-- `ofDigits` d'un `replicate m c` : `c * repunit060 m`. -/
theorem ofDigits_replicate (m c : ℕ) :
    Nat.ofDigits 10 (List.replicate m c) = c * repunit060 m := by
  unfold repunit060
  rw [← ofDigits_map_mul (List.replicate m 1) c]
  congr 1
  rw [List.map_replicate]
  congr 1
  exact (one_mul c).symm

/-- Les chiffres de `c * repunit060 m` sont `m` fois `c` (`1 <= c <= 9`,
    `m >= 1`). -/
theorem digits_mul_repunit {c m : ℕ} (hc0 : 1 ≤ c) (hc9 : c ≤ 9)
    (hm : 1 ≤ m) : Nat.digits 10 (c * repunit060 m) = List.replicate m c := by
  rw [← ofDigits_replicate m c]
  apply Nat.digits_ofDigits 10 (by norm_num)
  · intro l hl
    have := (List.mem_replicate.mp hl).2
    omega
  · intro h
    obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : m ≠ 0)
    rw [List.getLast_replicate_succ]
    omega

/-- Les chiffres de `repunit060 m` sont `m` fois `1` (`m >= 1`). -/
theorem digits_repunit {m : ℕ} (hm : 1 ≤ m) :
    Nat.digits 10 (repunit060 m) = List.replicate m 1 := by
  rw [show repunit060 m = 1 * repunit060 m from (one_mul _).symm]
  exact digits_mul_repunit (by norm_num) (by norm_num) hm

/-- **Classification structurelle** : `n` est un repdigit ssi
    `n = c * repunit060 m` avec `c <= 9` et `m >= 1` (`n = 0` vient de
    `c = 0`). C'est le levier des comptages certifies : sous `10 ^ k`,
    il n'y a que `9 * k` candidats repdigits positifs. -/
theorem isRepdigit_iff {n : ℕ} :
    IsRepdigit n ↔ ∃ c : ℕ, c ≤ 9 ∧
      ∃ m : ℕ, 1 ≤ m ∧ n = c * repunit060 m := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := isRepdigit_iff_replicate.mp h
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact ⟨0, by norm_num, 1, by norm_num, by simp [repunit060]⟩
    · have hne : Nat.digits 10 n ≠ [] :=
        Nat.digits_ne_nil_iff_ne_zero.mpr (by omega)
      have hlen : 1 ≤ (Nat.digits 10 n).length := by
        rw [Nat.succ_le_iff, List.length_pos_iff]
        exact hne
      obtain ⟨d, hd⟩ := List.exists_mem_of_ne_nil _ hne
      have hdc : d = c := by
        have hd2 : d ∈ List.replicate (Nat.digits 10 n).length c := hc ▸ hd
        exact (List.mem_replicate.mp hd2).2
      have hc9 : c ≤ 9 := by
        have hlt := Nat.digits_lt_base (by norm_num : (1:ℕ) < 10) hd
        omega
      refine ⟨c, hc9, (Nat.digits 10 n).length, hlen, ?_⟩
      calc n = Nat.ofDigits 10 (Nat.digits 10 n) :=
            (Nat.ofDigits_digits 10 n).symm
        _ = Nat.ofDigits 10 (List.replicate (Nat.digits 10 n).length c) :=
            by conv_lhs => rw [hc]
        _ = c * repunit060 (Nat.digits 10 n).length := ofDigits_replicate _ _
  · rintro ⟨c, hc9, m, hm1, rfl⟩
    rcases Nat.eq_zero_or_pos c with rfl | hc0
    · rw [Nat.zero_mul]
      intro d hd
      simp [Nat.digits_zero] at hd
    · have hd : Nat.digits 10 (c * repunit060 m) = List.replicate m c :=
        digits_mul_repunit hc0 hc9 hm1
      intro d hd' e he'
      rw [hd, List.mem_replicate] at hd' he'
      rw [hd'.2, he'.2]

/-- Le produit de chiffres de `c * repunit060 m` est `c ^ m` - le fait
    clef de la conjecture de Krizek. -/
theorem digitProd_mul_repunit {c m : ℕ} (hc0 : 1 ≤ c) (hc9 : c ≤ 9)
    (hm : 1 ≤ m) : digitProd (c * repunit060 m) = c ^ m := by
  unfold digitProd
  rw [digits_mul_repunit hc0 hc9 hm, List.prod_replicate]

/-- Le produit de chiffres d'un repunit060 est `1`. -/
theorem digitProd_repunit {m : ℕ} (hm : 1 ≤ m) : digitProd (repunit060 m) = 1 := by
  rw [show repunit060 m = 1 * repunit060 m from (one_mul _).symm,
    digitProd_mul_repunit (by norm_num) (by norm_num) hm, one_pow]

/-- **Reduction de Krizek** : pour `1 <= c <= 9` et `m >= 1`, le
    repdigit `c * repunit060 m` est dans la suite ssi `c ^ m` est repdigit.
    Les non-repunits de la suite sont donc exactement les
    `c * repunit060 m` avec `c ^ m` repdigit `>= 10` ou... la conjecture
    dit : jamais pour `m >= 4`. -/
theorem inSeq_mul_repunit {c m : ℕ} (hc0 : 1 ≤ c) (hc9 : c ≤ 9)
    (hm : 1 ≤ m) : InSeq (c * repunit060 m) ↔ IsRepdigit (c ^ m) := by
  have hd : Nat.digits 10 (c * repunit060 m) = List.replicate m c :=
    digits_mul_repunit hc0 hc9 hm
  have hprod : digitProd (c * repunit060 m) = c ^ m := by
    unfold digitProd
    rw [hd, List.prod_replicate]
  constructor
  · intro h
    have := h.2
    rw [hprod] at this
    exact this
  · intro h
    refine ⟨?_, ?_⟩
    · intro d hd' e he'
      rw [hd, List.mem_replicate] at hd' he'
      rw [hd'.2, he'.2]
    · rw [hprod]
      exact h

/-- **Famille infinie** : tout repunit060 `repunit060 m` (`m >= 1`) est dans
    la suite (produit `1`, repdigit). -/
theorem inSeq_repunit {m : ℕ} (hm : 1 ≤ m) : InSeq (repunit060 m) := by
  rw [show repunit060 m = 1 * repunit060 m from (one_mul _).symm]
  apply (inSeq_mul_repunit (by norm_num) (by norm_num) hm).mpr
  rw [one_pow]
  exact isRepdigit_of_lt_ten (by norm_num)

/-- Tout `n < 10` est dans la suite (repdigit, produit `n` repdigit -
    ou `1` pour `n = 0`). -/
theorem inSeq_of_lt_ten {n : ℕ} (hn : n < 10) : InSeq n := by
  refine ⟨isRepdigit_of_lt_ten hn, ?_⟩
  rcases Nat.eq_zero_or_pos n with rfl | h0
  · have hp : digitProd 0 = 1 := rfl
    rw [hp]
    exact isRepdigit_of_lt_ten (by norm_num)
  · have hd : Nat.digits 10 n = [n] := Nat.digits_of_lt 10 n (by omega) hn
    have hp : digitProd n = n := by
      unfold digitProd
      rw [hd]
      exact List.prod_singleton
    rw [hp]
    exact isRepdigit_of_lt_ten hn

/-- Les termes composes certifies : `11 = repunit060 2`. -/
theorem inSeq_11 : InSeq 11 := inSeq_repunit (m := 2) (by norm_num)

/-- `22 = 2 * repunit060 2`, produit `4` repdigit. -/
theorem inSeq_22 : InSeq 22 :=
  (inSeq_mul_repunit (c := 2) (m := 2) (by norm_num) (by norm_num)
    (by norm_num)).mpr (isRepdigit_of_lt_ten (by decide))

/-- `33 = 3 * repunit060 2`, produit `9` repdigit. -/
theorem inSeq_33 : InSeq 33 :=
  (inSeq_mul_repunit (c := 3) (m := 2) (by norm_num) (by norm_num)
    (by norm_num)).mpr (isRepdigit_of_lt_ten (by decide))

/-- `111 = repunit060 3`. -/
theorem inSeq_111 : InSeq 111 := inSeq_repunit (m := 3) (by norm_num)

/-- `222 = 2 * repunit060 3`, produit `8` repdigit. -/
theorem inSeq_222 : InSeq 222 :=
  (inSeq_mul_repunit (c := 2) (m := 3) (by norm_num) (by norm_num)
    (by norm_num)).mpr (isRepdigit_of_lt_ten (by decide))

/-- `1111 = repunit060 4` - le premier repunit060 au-dela des exceptions. -/
theorem inSeq_1111 : InSeq 1111 := inSeq_repunit (m := 4) (by norm_num)

/-- `11111 = repunit060 5`. -/
theorem inSeq_11111 : InSeq 11111 := inSeq_repunit (m := 5) (by norm_num)



/-- La suite est infinie : les repunits `repunit060 m` (`m >= 1`) sont
    tous dans `InSeq` et `repunit060` est injective. -/
theorem inSeq_infinite : (Set.ofPred InSeq).Infinite := by
  apply Set.infinite_of_injective_forall_mem repunit060_strictMono.injective
  intro i
  show InSeq (repunit060 i)
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · rw [repunit060_zero]
    exact inSeq_of_lt_ten (by norm_num)
  · exact inSeq_repunit hi

/-- `a(n)` verifie le predicat du verbatim (`n >= 1`). -/
theorem a201060_mem (n : ℕ) (_hn : 1 ≤ n) : InSeq (a201060 n) := by
  unfold a201060
  exact Nat.nth_mem_of_infinite inSeq_infinite _

/-- L'enumeration est strictement croissante a partir de `n = 1`. -/
theorem a201060_strictMono {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    a201060 a < a201060 b := by
  unfold a201060
  rw [Nat.nth_lt_nth inSeq_infinite]
  omega

/-- Borne inferieure : `a(n) >= n - 1` (les `n - 1` elements
    precedents sont distincts et plus petits). -/
theorem a201060_ge (n : ℕ) : n - 1 ≤ a201060 n := by
  unfold a201060
  exact (Nat.nth_strictMono inSeq_infinite).id_le (n - 1)

/-- Certificat de comptage : si les elements de `InSeq` en dessous de
    `v` sont exactement la liste `L` (sans doublons), alors
    `Nat.count InSeq v = L.length`. Evite tout balayage de `[0, v)`. -/
theorem count_eq_of_list {v : ℕ} {L : List ℕ}
    (hmem : ∀ n, (n < v ∧ InSeq n) ↔ n ∈ L)
    (hnodup : L.Nodup) : Nat.count InSeq v = L.length := by
  rw [Nat.count_eq_card_filter_range]
  have hfin : {x ∈ Finset.range v | InSeq x} = L.toFinset := by
    ext x
    rw [Finset.mem_filter, Finset.mem_range, List.mem_toFinset]
    exact hmem x
  rw [hfin, List.toFinset_card_of_nodup hnodup]

/-- La liste triee des elements de la suite en dessous de `11111` :
    les 16 termes {0..9, 11, 22, 33, 111, 222, 1111} - exactement les
    16 premiers termes OEIS. -/
def seqBelow : List ℕ :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 11, 22, 33, 111, 222, 1111]

/-- `seqBelow` est sans doublons. -/
theorem seqBelow_nodup : seqBelow.Nodup := by decide

/-- Tout element de `seqBelow` est dans la suite (certificats
    structurels : `inSeq_of_lt_ten`, repunits, `c * repunit060 m`). -/
theorem inSeq_of_mem {n : ℕ} (h : n ∈ seqBelow) : InSeq n := by
  simp only [seqBelow, List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | exact inSeq_of_lt_ten (by decide)
      | exact inSeq_11
      | exact inSeq_22
      | exact inSeq_33
      | exact inSeq_111
      | exact inSeq_222
      | exact inSeq_1111

/-- **Classification** : en dessous de `11111`, les elements de la
    suite sont EXACTEMENT les 16 elements de `seqBelow`. Preuve :
    `n = c * repunit060 m` (structure), `m <= 4` car `repunit060 5 = 11111`,
    puis verification des `9 * 4 + 1 = 37` candidats par `decide` -
    le seul endroit ou le kernel evalue `Nat.digits`, sur des
    arguments <= 4 chiffres. -/
theorem inSeq_mem_of_lt {n : ℕ} (hv : n < 11111) (hs : InSeq n) :
    n ∈ seqBelow := by
  obtain ⟨c, hc9, m, hm1, rfl⟩ := isRepdigit_iff.mp hs.1
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [Nat.zero_mul]
    decide
  · have hm4 : m ≤ 4 := by
      by_contra hm
      have hm5 : 5 ≤ m := by omega
      have h1 : repunit060 5 ≤ repunit060 m := repunit060_strictMono.monotone hm5
      have h2 : repunit060 m ≤ c * repunit060 m := Nat.le_mul_of_pos_left _ hc0
      have h3 : repunit060 5 = 11111 := by decide
      omega
    interval_cases c <;> interval_cases m <;> revert hv hs <;> decide

/-- Le comptage sous `v` (`v <= 11111`) est la longueur du prefixe de
    `seqBelow` inferieur a `v` - certificat kernel-pur. -/
theorem count_eq_filter (v : ℕ) (hv : v ≤ 11111) :
    Nat.count InSeq v =
      (seqBelow.filter (fun x => decide (x < v))).length := by
  apply count_eq_of_list
  · intro n
    rw [List.mem_filter]
    constructor
    · intro ⟨hnv, hs⟩
      refine ⟨inSeq_mem_of_lt (lt_of_lt_of_le hnv hv) hs, ?_⟩
      rw [decide_eq_true_eq]
      exact hnv
    · intro hnf
      rw [decide_eq_true_eq] at hnf
      exact ⟨hnf.2, inSeq_of_mem hnf.1⟩
  · exact List.Nodup.filter _ seqBelow_nodup

/-- `a(count(v) + 1) = v` pour `v` dans la suite : la traduction
    OEIS `a(k)` = k-ieme terme (`Nat.nth_count`). -/
theorem a201060_succ_count {v : ℕ} (hv : InSeq v) :
    a201060 (Nat.count InSeq v + 1) = v := by
  unfold a201060
  rw [Nat.add_sub_cancel]
  exact Nat.nth_count hv

/-- Au moins `n` elements de la suite sont `<= repunit060 n` : les `n`
    repunits `repunit060 1, ..., repunit060 n` (injectivite de `repunit060`). -/
theorem count_repunit_succ (n : ℕ) :
    n ≤ Nat.count InSeq (repunit060 n + 1) := by
  rw [Nat.count_eq_card_filter_range]
  have hsub : (Finset.Icc 1 n).image repunit060 ⊆
      Finset.filter (fun x => InSeq x) (Finset.range (repunit060 n + 1)) := by
    intro x hx
    rw [Finset.mem_image] at hx
    obtain ⟨i, hi, rfl⟩ := hx
    rw [Finset.mem_Icc] at hi
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨?_, inSeq_repunit hi.1⟩
    have hmono := repunit060_strictMono.monotone hi.2
    omega
  calc (n : ℕ) = (Finset.Icc 1 n).card := by
        rw [Nat.card_Icc, Nat.add_sub_cancel]
    _ = ((Finset.Icc 1 n).image repunit060).card :=
        (Finset.card_image_of_injective _ repunit060_strictMono.injective).symm
    _ ≤ (Finset.filter (fun x => InSeq x)
          (Finset.range (repunit060 n + 1))).card :=
        Finset.card_le_card hsub

/-- **Borne superieure structurelle** : `a(n) <= repunit060 n` (`n >= 1`) -
    les `n` repunits `repunit060 1, ..., repunit060 n` sont `n` elements de
    la suite `<= repunit060 n`, donc le n-ieme terme ne les depasse pas.
    La conjecture de Krizek predit l'egalite pour `n >= 16`. -/
theorem a201060_le_repunit {n : ℕ} (hn : 1 ≤ n) : a201060 n ≤ repunit060 n := by
  have hc := count_repunit_succ n
  have h := Nat.nth_lt_of_lt_count (p := InSeq)
    (show n - 1 < Nat.count InSeq (repunit060 n + 1) by omega)
  unfold a201060
  omega

/-! ### Ancres certifiees : les 17 premiers termes OEIS

`a(k+1) = v` se prouve par `a201060_succ_count` (`InSeq v` certifie)
plus `Nat.count InSeq v = k` via `count_eq_filter` (comptage sur la
liste `seqBelow`, aucun balayage de segment). -/

/-- `a(1) = 0` : `0` a tous ses chiffres egaux (liste vide) et son
    produit `1` est repdigit. -/
theorem a201060_1 : a201060 1 = 0 := by
  have hc : Nat.count InSeq 0 = 0 := Nat.count_zero _
  rw [show (1 : ℕ) = Nat.count InSeq 0 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(2) = 1`. -/
theorem a201060_2 : a201060 2 = 1 := by
  have hc : Nat.count InSeq 1 = 1 := by
    rw [count_eq_filter 1 (by norm_num)]
    decide
  rw [show (2 : ℕ) = Nat.count InSeq 1 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(3) = 2`. -/
theorem a201060_3 : a201060 3 = 2 := by
  have hc : Nat.count InSeq 2 = 2 := by
    rw [count_eq_filter 2 (by norm_num)]
    decide
  rw [show (3 : ℕ) = Nat.count InSeq 2 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(4) = 3`. -/
theorem a201060_4 : a201060 4 = 3 := by
  have hc : Nat.count InSeq 3 = 3 := by
    rw [count_eq_filter 3 (by norm_num)]
    decide
  rw [show (4 : ℕ) = Nat.count InSeq 3 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(5) = 4`. -/
theorem a201060_5 : a201060 5 = 4 := by
  have hc : Nat.count InSeq 4 = 4 := by
    rw [count_eq_filter 4 (by norm_num)]
    decide
  rw [show (5 : ℕ) = Nat.count InSeq 4 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(6) = 5`. -/
theorem a201060_6 : a201060 6 = 5 := by
  have hc : Nat.count InSeq 5 = 5 := by
    rw [count_eq_filter 5 (by norm_num)]
    decide
  rw [show (6 : ℕ) = Nat.count InSeq 5 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(7) = 6`. -/
theorem a201060_7 : a201060 7 = 6 := by
  have hc : Nat.count InSeq 6 = 6 := by
    rw [count_eq_filter 6 (by norm_num)]
    decide
  rw [show (7 : ℕ) = Nat.count InSeq 6 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(8) = 7`. -/
theorem a201060_8 : a201060 8 = 7 := by
  have hc : Nat.count InSeq 7 = 7 := by
    rw [count_eq_filter 7 (by norm_num)]
    decide
  rw [show (8 : ℕ) = Nat.count InSeq 7 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(9) = 8`. -/
theorem a201060_9 : a201060 9 = 8 := by
  have hc : Nat.count InSeq 8 = 8 := by
    rw [count_eq_filter 8 (by norm_num)]
    decide
  rw [show (9 : ℕ) = Nat.count InSeq 8 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(10) = 9` : fin du prefixe `0..9`. -/
theorem a201060_10 : a201060 10 = 9 := by
  have hc : Nat.count InSeq 9 = 9 := by
    rw [count_eq_filter 9 (by norm_num)]
    decide
  rw [show (10 : ℕ) = Nat.count InSeq 9 + 1 by omega]
  exact a201060_succ_count (inSeq_of_lt_ten (by norm_num))

/-- `a(11) = 11 = repunit060 2` : le premier repdigit a deux chiffres
    de la suite (produit `1`). -/
theorem a201060_11 : a201060 11 = 11 := by
  have hc : Nat.count InSeq 11 = 10 := by
    rw [count_eq_filter 11 (by norm_num)]
    decide
  rw [show (11 : ℕ) = Nat.count InSeq 11 + 1 by omega]
  exact a201060_succ_count inSeq_11

/-- `a(12) = 22` (produit `4`, repdigit). -/
theorem a201060_12 : a201060 12 = 22 := by
  have hc : Nat.count InSeq 22 = 11 := by
    rw [count_eq_filter 22 (by norm_num)]
    decide
  rw [show (12 : ℕ) = Nat.count InSeq 22 + 1 by omega]
  exact a201060_succ_count inSeq_22

/-- `a(13) = 33` (produit `9`, repdigit ; `44` est exclu car `16`
    n'est pas repdigit). -/
theorem a201060_13 : a201060 13 = 33 := by
  have hc : Nat.count InSeq 33 = 12 := by
    rw [count_eq_filter 33 (by norm_num)]
    decide
  rw [show (13 : ℕ) = Nat.count InSeq 33 + 1 by omega]
  exact a201060_succ_count inSeq_33

/-- `a(14) = 111 = repunit060 3`. -/
theorem a201060_14 : a201060 14 = 111 := by
  have hc : Nat.count InSeq 111 = 13 := by
    rw [count_eq_filter 111 (by norm_num)]
    decide
  rw [show (14 : ℕ) = Nat.count InSeq 111 + 1 by omega]
  exact a201060_succ_count inSeq_111

/-- `a(15) = 222` (produit `8`, repdigit) : le dernier terme non
    repunit060 publie - toute la conjecture tient dans `n >= 16`. -/
theorem a201060_15 : a201060 15 = 222 := by
  have hc : Nat.count InSeq 222 = 14 := by
    rw [count_eq_filter 222 (by norm_num)]
    decide
  rw [show (15 : ℕ) = Nat.count InSeq 222 + 1 by omega]
  exact a201060_succ_count inSeq_222

/-- `a(16) = 1111 = repunit060 4` : premier repunit060 de la zone
    conjecturee (`n >= 16`, Krizek). -/
theorem a201060_16 : a201060 16 = 1111 := by
  have hc : Nat.count InSeq 1111 = 15 := by
    rw [count_eq_filter 1111 (by norm_num)]
    decide
  rw [show (16 : ℕ) = Nat.count InSeq 1111 + 1 by omega]
  exact a201060_succ_count inSeq_1111

/-- `a(17) = 11111 = repunit060 5`. -/
theorem a201060_17 : a201060 17 = 11111 := by
  have hc : Nat.count InSeq 11111 = 16 := by
    rw [count_eq_filter 11111 (by norm_num)]
    decide
  rw [show (17 : ℕ) = Nat.count InSeq 11111 + 1 by omega]
  exact a201060_succ_count inSeq_11111

/-- **Theoreme structurel** : `a201060` capture exactement le verbatim
    (le n-ieme repdigit a produit repdigit, offset 1) ; chaque terme
    verifie le predicat (`a201060_mem`) ; l'enumeration est strictement
    croissante (`a201060_strictMono`) ; bornes structurelles
    `n - 1 <= a(n) <= repunit060 n` ; et les ancres `a(16) = 1111`,
    `a(17) = 11111` confirment les donnees OEIS au seuil de Krizek.
    (Renomme `A201060_anchors` lors de la promotion : le nom `A201060`
    designe desormais la conjecture de Krizek PROUVEE plus bas.) -/
theorem A201060_anchors :
    (∀ n : ℕ, 1 ≤ n → InSeq (a201060 n))
      ∧ (∀ a b : ℕ, 1 ≤ a → a < b → a201060 a < a201060 b)
      ∧ (∀ n : ℕ, 1 ≤ n → n - 1 ≤ a201060 n ∧ a201060 n ≤ repunit060 n)
      ∧ a201060 16 = 1111 ∧ a201060 17 = 11111 :=
  ⟨a201060_mem,
    fun _a _b => a201060_strictMono,
    fun n hn => ⟨a201060_ge n, a201060_le_repunit hn⟩,
    a201060_16, a201060_17⟩



/-! ### Promotion ATK (2026-11-12) : la conjecture de Krizek est PROUVEE

Le contenu ci-dessous est la chaine integrale promue depuis
`Check_atk_A201060.lean` (run lean-run-gh 43115106721 vert, sha
77ff16f, axiomes trio) : certificat fini elementaire - pour tout `c`
dans `2..9`, aucun repunit `R_k` (`k >= 2`) ne divise `c^m` - puis
couverture `repunit060_of_inSeq` : tout terme `>= 1111` de la suite
est un repunit060, et `a(n) >= 1111` des `n >= 16`. -/

section AtkA201060

/-- Decomposition bloc des repunits : `R_{a+b} = R_b + 10^b * R_a`. -/
theorem repunit060_add (a b : ℕ) :
    repunit060 (a + b) = repunit060 b + 10 ^ b * repunit060 a := by
  induction b with
  | zero => simp [repunit060_zero]
  | succ k ih =>
    rw [Nat.add_succ, repunit060_succ, ih, repunit060_succ]
    ring

/-- Divisibilite bloc : `R_a` divise `R_{a*q}` pour tout `q`. -/
theorem repunit060_dvd_mul (a q : ℕ) : repunit060 a ∣ repunit060 (a * q) := by
  induction q with
  | zero => simp [repunit060_zero]
  | succ q ih =>
    rw [show a * (q + 1) = a * q + a from by ring, repunit060_add]
    obtain ⟨t, ht⟩ := ih
    exact dvd_add dvd_rfl ⟨t * 10 ^ a, by rw [ht]; ring⟩

/-- Periodicite modulaire : si `d | R_p` et `d | 10^p - 1`, alors
    `R_{k+p} % d = R_k % d`. -/
theorem repunit060_mod_period {d p : ℕ} (hR : d ∣ repunit060 p)
    (h10 : d ∣ 10 ^ p - 1) (k : ℕ) :
    repunit060 (k + p) % d = repunit060 k % d := by
  obtain ⟨t, ht⟩ := hR
  obtain ⟨s, hs⟩ := h10
  have h10le : 0 < 10 ^ p := by positivity
  have hp10 : 10 ^ p = 10 ^ p - 1 + 1 := (Nat.sub_add_cancel h10le).symm
  rw [repunit060_add, hp10, hs, ht]
  have e : d * t + (d * s + 1) * repunit060 k =
      repunit060 k + d * (t + s * repunit060 k) := by ring
  rw [e, Nat.add_mul_mod_self_left]

/-- Iteration de la periodicite : `R_{p*q+r} % d = R_r % d`. -/
theorem repunit060_mod_cycle {d p : ℕ} (hR : d ∣ repunit060 p)
    (h10 : d ∣ 10 ^ p - 1) (q r : ℕ) :
    repunit060 (p * q + r) % d = repunit060 r % d := by
  induction q with
  | zero => simp
  | succ q ih =>
    rw [show p * (q + 1) + r = p * q + r + p from by ring,
      repunit060_mod_period hR h10, ih]

/-- Reduction modulo 7 : `R_k % 7 = R_{k % 6} % 7`
    (`R_6 = 111111 = 7 * 15873`, `10^6 = 7 * 142857 + 1`). -/
theorem repunit060_mod_seven (k : ℕ) :
    repunit060 k % 7 = repunit060 (k % 6) % 7 := by
  have e : k = 6 * (k / 6) + k % 6 := by omega
  conv_lhs => rw [e]
  exact repunit060_mod_cycle (d := 7) (p := 6)
    (show (7 : ℕ) ∣ repunit060 6 by decide)
    (show (7 : ℕ) ∣ 10 ^ 6 - 1 by decide) (k / 6) (k % 6)

/-- `7 | R_k` ssi `6 | k` : les restes de `R_0..R_5` mod 7 sont
    `0, 1, 4, 6, 5, 2` - seul le reste `0` en `k % 6 = 0`. -/
theorem seven_dvd_repunit060_iff (k : ℕ) : 7 ∣ repunit060 k ↔ 6 ∣ k := by
  rw [Nat.dvd_iff_mod_eq_zero, repunit060_mod_seven, Nat.dvd_iff_mod_eq_zero]
  have hr : k % 6 < 6 := Nat.mod_lt k (by norm_num)
  rcases (show k % 6 = 0 ∨ k % 6 = 1 ∨ k % 6 = 2 ∨ k % 6 = 3 ∨
      k % 6 = 4 ∨ k % 6 = 5 from by omega) with h | h | h | h | h | h <;>
    rw [h] <;> decide

/-- Reduction modulo 3 : `R_k % 3 = k % 3` (`R_{j+1} = 1 + 10 R_j`,
    `10 = 1 [3]`). -/
theorem repunit060_mod_three (k : ℕ) : repunit060 k % 3 = k % 3 := by
  induction k with
  | zero => rfl
  | succ j ih =>
    rw [repunit060_succ]
    omega

/-- `3 | R_k` ssi `3 | k`. -/
theorem three_dvd_repunit060_iff (k : ℕ) : 3 ∣ repunit060 k ↔ 3 ∣ k := by
  rw [Nat.dvd_iff_mod_eq_zero, repunit060_mod_three]
  exact Nat.dvd_iff_mod_eq_zero.symm

/-- `R_k` est impair des que `k >= 1` (`R_{j+1} = 1 + 10 R_j`). -/
theorem repunit060_mod_two {k : ℕ} (hk : 1 ≤ k) : repunit060 k % 2 = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [repunit060_succ]
  omega

/-- `R_k % 5 = 1` des que `k >= 1`. -/
theorem repunit060_mod_five {k : ℕ} (hk : 1 ≤ k) : repunit060 k % 5 = 1 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  rw [repunit060_succ]
  omega

/-- `2` ne divise pas `R_k` (`k >= 1`). -/
theorem two_not_dvd_repunit060 {k : ℕ} (hk : 1 ≤ k) : ¬ 2 ∣ repunit060 k := by
  rw [Nat.dvd_iff_mod_eq_zero, repunit060_mod_two hk]
  omega

/-- `5` ne divise pas `R_k` (`k >= 1`). -/
theorem five_not_dvd_repunit060 {k : ℕ} (hk : 1 ≤ k) : ¬ 5 ∣ repunit060 k := by
  rw [Nat.dvd_iff_mod_eq_zero, repunit060_mod_five hk]
  omega

/-- Coprimalite a un premier qui ne divise pas. -/
theorem coprime_of_prime_not_dvd {p u : ℕ} (hp : p.Prime) (h : ¬ p ∣ u) :
    Nat.Coprime u p :=
  Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr h)

/-- Lemme d'elimination generique : si `gcd (R_k, P) = 1` et `R_k | P`,
    alors `R_k <= 1` (contredit `R_k >= 11` a chaque usage). -/
theorem repunit060_le_one_of_coprime_dvd {k P : ℕ}
    (hcop : Nat.Coprime (repunit060 k) P) (hdiv : repunit060 k ∣ P) :
    repunit060 k ≤ 1 := by
  have hgcd : Nat.gcd (repunit060 k) P = 1 := hcop
  have h1 : repunit060 k ∣ 1 := by
    rw [← hgcd]
    exact Nat.dvd_gcd (dvd_refl _) hdiv
  exact Nat.le_of_dvd (by norm_num) h1

/-- **Structure 3-adique** : si `R_k | P` avec `R_k >= 11`, que tout `u`
    premier a `3` est premier a `P`, et que `gcd (37, P) = 1`, alors
    absurde. Preuve : `3 | R_k` (sinon `R_k <= 1`), donc `3 | k`, donc
    `k = 3 q`, donc `R_3 = 111 | R_{3q} = R_k | P`, donc `37 | P` -
    absurde. Couvre `P = 3^m` (cas `c = 3`, `c = 6`) et `P = 9^m`
    (cas `c = 9`). -/
theorem repunit060_dvd_power_of_three_false {k P : ℕ}
    (hge : 11 ≤ repunit060 k)
    (hcop : ∀ u : ℕ, Nat.Coprime u 3 → Nat.Coprime u P)
    (h37 : Nat.Coprime 37 P)
    (hdiv : repunit060 k ∣ P) : False := by
  have h3 : 3 ∣ repunit060 k := by
    by_contra h3n
    have hc3 : Nat.Coprime (repunit060 k) 3 :=
      coprime_of_prime_not_dvd (by norm_num) h3n
    have hle : repunit060 k ≤ 1 :=
      repunit060_le_one_of_coprime_dvd (hcop _ hc3) hdiv
    omega
  have h3k : 3 ∣ k := (three_dvd_repunit060_iff k).mp h3
  obtain ⟨q, rfl⟩ := h3k
  have h111 : (111 : ℕ) ∣ repunit060 (3 * q) := by
    have hR3 : repunit060 3 = 111 := by decide
    rw [← hR3]
    exact repunit060_dvd_mul 3 q
  have h37d : (37 : ℕ) ∣ P :=
    dvd_trans (dvd_trans (by decide : (37 : ℕ) ∣ 111) h111) hdiv
  have hgcd37 : Nat.gcd 37 P = 1 := h37
  have h371 : (37 : ℕ) ∣ 1 := by
    rw [← hgcd37]
    exact Nat.dvd_gcd (dvd_refl _) h37d
  have h37le : (37 : ℕ) ≤ 1 := Nat.le_of_dvd (by norm_num) h371
  omega

/-- **Structure 7-adique** : `R_k | 7^m` est impossible pour `R_k >= 11`.
    Preuve : `7 | R_k` (sinon `R_k <= 1`), donc `6 | k`, donc `2 | k`,
    donc `R_2 = 11 | R_k | 7^m` - absurde car `gcd (11, 7^m) = 1`. -/
theorem repunit060_dvd_seven_pow_false {k m : ℕ}
    (hge : 11 ≤ repunit060 k) (hdiv : repunit060 k ∣ 7 ^ m) : False := by
  have h7 : 7 ∣ repunit060 k := by
    by_contra h7n
    have hc7 : Nat.Coprime (repunit060 k) 7 :=
      coprime_of_prime_not_dvd (by norm_num) h7n
    have hle : repunit060 k ≤ 1 :=
      repunit060_le_one_of_coprime_dvd (hc7.pow_right m) hdiv
    omega
  have h6k : 6 ∣ k := (seven_dvd_repunit060_iff k).mp h7
  obtain ⟨q, rfl⟩ := h6k
  obtain ⟨q2, hq2⟩ : ∃ q2 : ℕ, 6 * q = 2 * q2 := ⟨3 * q, by ring⟩
  have h11 : (11 : ℕ) ∣ repunit060 (6 * q) := by
    rw [hq2]
    have hR2 : repunit060 2 = 11 := by decide
    rw [← hR2]
    exact repunit060_dvd_mul 2 q2
  have h11B : (11 : ℕ) ∣ 7 ^ m := dvd_trans h11 hdiv
  have hc11 : Nat.Coprime 11 (7 ^ m) :=
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 11)).mpr
      (by decide : ¬ (11 : ℕ) ∣ 7)).pow_right m
  have hgcd11 : Nat.gcd 11 (7 ^ m) = 1 := hc11
  have h111 : (11 : ℕ) ∣ 1 := by
    rw [← hgcd11]
    exact Nat.dvd_gcd (dvd_refl _) h11B
  have h11le : (11 : ℕ) ≤ 1 := Nat.le_of_dvd (by norm_num) h111
  omega

/-- **Certificat fini d'elimination** : aucun `c^m` avec `c` dans
    `{2,..,9}` n'est divisible par un repunit `R_k`, `k >= 2`.
    Coeur arithmetique de la conjecture de Krizek. -/
theorem repunit060_not_dvd_small_pow {c m : ℕ} (hc2 : 2 ≤ c) (hc9 : c ≤ 9)
    {k : ℕ} (hk2 : 2 ≤ k) (hdiv : repunit060 k ∣ c ^ m) : False := by
  have hge : 11 ≤ repunit060 k := by
    have hR2 : repunit060 2 = 11 := by decide
    have hm := repunit060_strictMono.monotone hk2
    omega
  have hk1 : 1 ≤ k := by omega
  interval_cases c
  · -- c = 2 : `R_k` impair, `gcd (R_k, 2^m) = 1`, `R_k | 2^m` -> `R_k <= 1`
    have hc2m : Nat.Coprime (repunit060 k) (2 ^ m) :=
      (coprime_of_prime_not_dvd (by norm_num)
        (two_not_dvd_repunit060 hk1)).pow_right m
    have hle := repunit060_le_one_of_coprime_dvd hc2m hdiv
    omega
  · -- c = 3 : `R_k | 3^m`, structure 3-adique (`P = 3^m`)
    exact repunit060_dvd_power_of_three_false hge
      (fun _u hu => hu.pow_right m)
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 37)).mpr
        (by decide : ¬ (37 : ℕ) ∣ 3) |>.pow_right m)
      hdiv
  · -- c = 4 = 2*2 : `R_k | 2^m * 2^m`, Euclide -> `R_k | 2^m`
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow] at hdiv
    have hc2m : Nat.Coprime (repunit060 k) (2 ^ m) :=
      (coprime_of_prime_not_dvd (by norm_num)
        (two_not_dvd_repunit060 hk1)).pow_right m
    have h2m : repunit060 k ∣ 2 ^ m := hc2m.dvd_of_dvd_mul_left hdiv
    have hle := repunit060_le_one_of_coprime_dvd hc2m h2m
    omega
  · -- c = 5 : `gcd (R_k, 5^m) = 1`, `R_k | 5^m` -> `R_k <= 1`
    have hc5m : Nat.Coprime (repunit060 k) (5 ^ m) :=
      (coprime_of_prime_not_dvd (by norm_num)
        (five_not_dvd_repunit060 hk1)).pow_right m
    have hle := repunit060_le_one_of_coprime_dvd hc5m hdiv
    omega
  · -- c = 6 = 2*3 : `R_k | 2^m * 3^m`, Euclide -> `R_k | 3^m`
    rw [show (6 : ℕ) = 2 * 3 by norm_num, mul_pow] at hdiv
    have hc2m : Nat.Coprime (repunit060 k) (2 ^ m) :=
      (coprime_of_prime_not_dvd (by norm_num)
        (two_not_dvd_repunit060 hk1)).pow_right m
    have h3m : repunit060 k ∣ 3 ^ m := hc2m.dvd_of_dvd_mul_left hdiv
    exact repunit060_dvd_power_of_three_false hge
      (fun _u hu => hu.pow_right m)
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 37)).mpr
        (by decide : ¬ (37 : ℕ) ∣ 3) |>.pow_right m)
      h3m
  · -- c = 7 : `R_k | 7^m`, structure 7-adique
    exact repunit060_dvd_seven_pow_false hge hdiv
  · -- c = 8 = 2*4 : Euclide x2 -> `R_k | 2^m`
    rw [show (8 : ℕ) = 2 * 4 by norm_num, mul_pow] at hdiv
    have hc2m : Nat.Coprime (repunit060 k) (2 ^ m) :=
      (coprime_of_prime_not_dvd (by norm_num)
        (two_not_dvd_repunit060 hk1)).pow_right m
    have h4m : repunit060 k ∣ 4 ^ m := hc2m.dvd_of_dvd_mul_left hdiv
    rw [show (4 : ℕ) = 2 * 2 by norm_num, mul_pow] at h4m
    have h2m : repunit060 k ∣ 2 ^ m := hc2m.dvd_of_dvd_mul_left h4m
    have hle := repunit060_le_one_of_coprime_dvd hc2m h2m
    omega
  · -- c = 9 : `R_k | 9^m`, structure 3-adique (`P = 9^m`, `gcd(37,9^m)=1`)
    exact repunit060_dvd_power_of_three_false hge
      (fun _u hu =>
        (show Nat.Coprime _u 9 from hu.mul_right hu).pow_right m)
      ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 37)).mpr
        (by decide : ¬ (37 : ℕ) ∣ 9) |>.pow_right m)
      hdiv

/-- **Lemme de couverture** : tout `x >= 1111` de la suite (repdigit a
    produit repdigit) est un repunit `repunit060 m`. Coeur de la
    conjecture : les seuls termes `>= 1111` sont les repunits. -/
theorem repunit060_of_inSeq {x : ℕ} (hx : InSeq x) (hge : 1111 ≤ x) :
    ∃ m : ℕ, x = repunit060 m := by
  obtain ⟨c, hc9, m, hm1, rfl⟩ := isRepdigit_iff.mp hx.1
  rcases Nat.eq_zero_or_pos c with rfl | hc0
  · rw [zero_mul] at hge
    exact absurd hge (by decide)
  by_cases hc1 : c = 1
  · subst hc1
    exact ⟨m, one_mul _⟩
  have hc2 : 2 ≤ c := by omega
  have hrep : IsRepdigit (c ^ m) := (inSeq_mul_repunit hc0 hc9 hm1).mp hx
  obtain ⟨d, hd9, k, hk1, hcd⟩ := isRepdigit_iff.mp hrep
  have hk2 : 2 ≤ k := by
    by_contra hkk
    have hkeq : k = 1 := by omega
    subst hkeq
    have hR1 : repunit060 1 = 1 := by decide
    rw [hR1, mul_one] at hcd
    have hcm9 : c ^ m ≤ 9 := by rw [hcd]; exact hd9
    have hm3 : m ≤ 3 := by
      by_contra hm
      have hm4 : 4 ≤ m := by omega
      have h2m : (2 : ℕ) ^ m ≤ c ^ m := by gcongr
      have h24 : (2 : ℕ) ^ 4 ≤ 2 ^ m := pow_le_pow_right' (by omega) hm4
      norm_num at h24
      omega
    have hm3' : repunit060 m ≤ repunit060 3 :=
      repunit060_strictMono.monotone hm3
    have hR3 : repunit060 3 = 111 := by decide
    have hle : c * repunit060 m ≤ 9 * 111 := by
      rw [← hR3]
      exact Nat.mul_le_mul hc9 hm3'
    omega
  have hdiv : repunit060 k ∣ c ^ m :=
    ⟨d, by rw [hcd]; exact mul_comm _ _⟩
  exact (repunit060_not_dvd_small_pow hc2 hc9 hk2 hdiv).elim

/-- **Conjecture de Krizek - PROUVEE** : `a(n)` est un repunit pour
    `n >= 16`. Enonce OEIS ouvert exact (`KrizekConjecture`), universel
    en `n`, kernel-pur, 0 sorry. -/
theorem atk_A201060 : KrizekConjecture := by
  intro n hn
  have hmem : InSeq (a201060 n) := a201060_mem n (by omega)
  have hge : 1111 ≤ a201060 n := by
    have h16 : a201060 16 = 1111 := a201060_16
    rcases Nat.eq_or_lt_of_le hn with h | h
    · subst h
      omega
    · have hlt : a201060 16 < a201060 n :=
        a201060_strictMono (by norm_num) h
      omega
  exact repunit060_of_inSeq hmem hge

end AtkA201060

/-- **Theoreme exporte - conjecture de Krizek PROUVEE** : `a(n)` est
    un repunit pour `n >= 16`. Enonce OEIS ouvert exact
    (`KrizekConjecture`), universel en `n`, kernel-pur, 0 sorry. -/
theorem A201060 : KrizekConjecture := atk_A201060

end OMA.A201060Port

theorem OMA.solution : type_of% @OMA.S_oeis_a201060.main :=
  OMA.A201060Port.atk_A201060
