import OMAStatements.S_oeis_a025757

-- Problem: A025757: 4th-order Vatalan numbers (generalization of Catalan numbers).
-- Upstream: formal-conjectures statements/oeis-a025757.lean:0 (declaration OMA.S_oeis_a025757.main)
-- Credit: @ivillar (the owner of the agent is credited as the solver)

/-! The generating function G satisfies a polynomial equation Phi(x, G) = 0. Differentiating it
repeatedly expresses the derivatives of G through G, with the partial derivative of Phi in G as
denominator. Substituting into the differential operator read off the recurrence and reducing
modulo Phi gives a polynomial identity, so the operator maps G to a polynomial rho. The
recurrence is the coefficient of a power of x in that equation, beyond the degree of rho. -/

namespace A025757Aux

open PowerSeries

theorem cnum (n : ℕ) [n.AtLeastTwo] :
    constantCoeff (OfNat.ofNat n : ℚ⟦X⟧) = (OfNat.ofNat n : ℚ) := map_ofNat constantCoeff n

theorem dnum (n : ℕ) [n.AtLeastTwo] : derivative ℚ (OfNat.ofNat n : ℚ⟦X⟧) = 0 := by
  rw [← Nat.cast_ofNat (R := ℚ⟦X⟧)]
  exact Derivation.map_natCast _ n

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem key (G : ℚ⟦X⟧)
    (hP : (16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G ^ 2 + (-27 : ℚ⟦X⟧) * G ^ 3 + (5 + X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    (5 * X ^ 3 - 239 * X ^ 4 + 3792 * X ^ 5 - 19712 * X ^ 6 - 4096 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-117 * X ^ 3 + 3672 * X ^ 4 - 27648 * X ^ 5 - 18432 * X ^ 6) * derivative ℚ (derivative ℚ G) + (192 * X ^ 3 - 2256 * X ^ 4 - 13056 * X ^ 5) * derivative ℚ G + (1968 * X ^ 3 - 384 * X ^ 4) * G =
      2592 * X ^ 3 := by
  have d4 : derivative ℚ (4 : ℚ⟦X⟧) = 0 := dnum 4
  have d5 : derivative ℚ (5 : ℚ⟦X⟧) = 0 := dnum 5
  have d8 : derivative ℚ (8 : ℚ⟦X⟧) = 0 := dnum 8
  have d12 : derivative ℚ (12 : ℚ⟦X⟧) = 0 := dnum 12
  have d16 : derivative ℚ (16 : ℚ⟦X⟧) = 0 := dnum 16
  have d20 : derivative ℚ (20 : ℚ⟦X⟧) = 0 := dnum 20
  have d27 : derivative ℚ (27 : ℚ⟦X⟧) = 0 := dnum 27
  have d48 : derivative ℚ (48 : ℚ⟦X⟧) = 0 := dnum 48
  have d54 : derivative ℚ (54 : ℚ⟦X⟧) = 0 := dnum 54
  have d60 : derivative ℚ (60 : ℚ⟦X⟧) = 0 := dnum 60
  have d81 : derivative ℚ (81 : ℚ⟦X⟧) = 0 := dnum 81
  have d108 : derivative ℚ (108 : ℚ⟦X⟧) = 0 := dnum 108
  have d162 : derivative ℚ (162 : ℚ⟦X⟧) = 0 := dnum 162
  have hp0 : (16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G * G + (-27 : ℚ⟦X⟧) * G * G * G + (5 + 1 * X : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hP
  have hL1 : derivative ℚ ((16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G * G + (-27 : ℚ⟦X⟧) * G * G * G + (5 + 1 * X : ℚ⟦X⟧) * G * G * G * G) =
      (-48 : ℚ⟦X⟧) * (derivative ℚ G) + (108 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-81 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 := by
    simp [Derivation.leibniz, d5, d16, d27, d48, d54]
    ring
  have hd1 : (-48 : ℚ⟦X⟧) * (derivative ℚ G) + (108 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-81 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G ^ 4 = 0 := by rw [← hL1, hp0, map_zero]
  have hp1 : (-48 : ℚ⟦X⟧) * (derivative ℚ G) + (108 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-81 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (20 + 4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G = 0 := by linear_combination hd1
  have hL2 : derivative ℚ ((-48 : ℚ⟦X⟧) * (derivative ℚ G) + (108 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-81 : ℚ⟦X⟧) * G * G * (derivative ℚ G) + (20 + 4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) + (1 : ℚ⟦X⟧) * G * G * G * G) =
      (-48 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (108 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (108 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-162 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-81 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (60 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) := by
    simp [Derivation.leibniz, d4, d20, d48, d81, d108]
    ring
  have hd2 : (-48 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (108 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (108 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-162 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (-81 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ G)) + (60 + 12 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) = 0 := by rw [← hL2, hp1, map_zero]
  have hp2 : (-48 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (108 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (108 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-162 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-81 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (60 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (20 + 4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G) = 0 := by linear_combination hd2
  have hL3 : derivative ℚ ((-48 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ G)) + (108 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ G) + (108 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ G)) + (-162 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ G) + (-81 : ℚ⟦X⟧) * G * G * (derivative ℚ (derivative ℚ G)) + (60 + 12 * X : ℚ⟦X⟧) * G * G * (derivative ℚ G) * (derivative ℚ G) + (20 + 4 * X : ℚ⟦X⟧) * G * G * G * (derivative ℚ (derivative ℚ G)) + (8 : ℚ⟦X⟧) * G * G * G * (derivative ℚ G)) =
      (-48 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (324 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-162 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (108 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-486 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (120 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-81 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (180 + 36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) := by
    simp [Derivation.leibniz, d4, d8, d12, d20, d48, d60, d81, d108, d162]
    ring
  have hd3 : (-48 : ℚ⟦X⟧) * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (324 : ℚ⟦X⟧) * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (-162 : ℚ⟦X⟧) * (derivative ℚ G) ^ 3 + (108 : ℚ⟦X⟧) * G * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (-486 : ℚ⟦X⟧) * G * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (120 + 24 * X : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 3 + (-81 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (180 + 36 * X : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) * (derivative ℚ (derivative ℚ G)) + (36 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ (derivative ℚ G))) + (12 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ (derivative ℚ G)) = 0 := by rw [← hL3, hp2, map_zero]
  have hfull : ((-48 : ℚ⟦X⟧) + (108 : ℚ⟦X⟧) * G + (-81 : ℚ⟦X⟧) * G ^ 2 + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3) ^ 5 * ((5 * X ^ 3 - 239 * X ^ 4 + 3792 * X ^ 5 - 19712 * X ^ 6 - 4096 * X ^ 7) * derivative ℚ (derivative ℚ (derivative ℚ G)) + (-117 * X ^ 3 + 3672 * X ^ 4 - 27648 * X ^ 5 - 18432 * X ^ 6) * derivative ℚ (derivative ℚ G) + (192 * X ^ 3 - 2256 * X ^ 4 - 13056 * X ^ 5) * derivative ℚ G + (1968 * X ^ 3 - 384 * X ^ 4) * G - (2592 * X ^ 3)) = 0 := by
    linear_combination ((41278242816 * X ^ 3 : ℚ⟦X⟧) + (-371886391296 * X ^ 3 + 6115295232 * X ^ 4 : ℚ⟦X⟧) * G + (1535607963648 * X ^ 3 - 50451185664 * X ^ 4 : ℚ⟦X⟧) * G ^ 2 + (-3841886453760 * X ^ 3 + 171992678400 * X ^ 4 : ℚ⟦X⟧) * G ^ 3 + (6484480303104 * X ^ 3 - 311099719680 * X ^ 4 + 1783627776 * X ^ 5 : ℚ⟦X⟧) * G ^ 4 + (-7776719124480 * X ^ 3 + 299362811904 * X ^ 4 - 11083972608 * X ^ 5 : ℚ⟦X⟧) * G ^ 5 + (6793503644160 * X ^ 3 - 85387198464 * X ^ 4 + 32965263360 * X ^ 5 : ℚ⟦X⟧) * G ^ 6 + (-4354604354304 * X ^ 3 - 145226317824 * X ^ 4 - 57187565568 * X ^ 5 : ℚ⟦X⟧) * G ^ 7 + (2032298680608 * X ^ 3 + 208690981632 * X ^ 4 + 60997681152 * X ^ 5 + 175177728 * X ^ 6 : ℚ⟦X⟧) * G ^ 8 + (-673332259464 * X ^ 3 - 133918583040 * X ^ 4 - 40373489664 * X ^ 5 - 740524032 * X ^ 6 : ℚ⟦X⟧) * G ^ 9 + (150296593014 * X ^ 3 + 48937921632 * X ^ 4 + 16144468992 * X ^ 5 + 967458816 * X ^ 6 : ℚ⟦X⟧) * G ^ 10 + (-20289236400 * X ^ 3 - 9877716720 * X ^ 4 - 3582620928 * X ^ 5 - 483729408 * X ^ 6 : ℚ⟦X⟧) * G ^ 11 + (1252422000 * X ^ 3 + 860220000 * X ^ 4 + 343096560 * X ^ 5 + 74089728 * X ^ 6 + 5971968 * X ^ 7 : ℚ⟦X⟧) * G ^ 12) * hP +
      ((1019215872 * X ^ 3 - 11975786496 * X ^ 4 - 69306679296 * X ^ 5 : ℚ⟦X⟧) + (-1397440512 * X ^ 3 + 43858132992 * X ^ 4 - 330225942528 * X ^ 5 - 220150628352 * X ^ 6 : ℚ⟦X⟧) * (derivative ℚ G) + (313528320 * X ^ 3 - 14986653696 * X ^ 4 + 237779877888 * X ^ 5 - 1236054048768 * X ^ 6 - 256842399744 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) ^ 2 + (-9172942848 * X ^ 3 + 107782078464 * X ^ 4 + 623760113664 * X ^ 5 : ℚ⟦X⟧) * G + (11528884224 * X ^ 3 - 361829597184 * X ^ 4 + 2724364025856 * X ^ 5 + 1816242683904 * X ^ 6 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-2352291840 * X ^ 3 + 112452820992 * X ^ 4 - 1784612487168 * X ^ 5 + 9283740106752 * X ^ 6 + 1874677727232 * X ^ 7 - 10871635968 * X ^ 8 : ℚ⟦X⟧) * G * (derivative ℚ G) ^ 2 + (37838389248 * X ^ 3 - 444601073664 * X ^ 4 - 2573010468864 * X ^ 5 : ℚ⟦X⟧) * G ^ 2 + (-43203704832 * X ^ 3 + 1355449614336 * X ^ 4 - 10194101600256 * X ^ 5 - 6924552634368 * X ^ 6 - 40768634880 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (7936185600 * X ^ 3 - 379349671680 * X ^ 4 + 6018803159040 * X ^ 5 - 31287618109440 * X ^ 6 - 6501323243520 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) ^ 2 + (-94678253568 * X ^ 3 + 1114162200576 * X ^ 4 + 6410613030912 * X ^ 5 + 6794772480 * X ^ 6 : ℚ⟦X⟧) * G ^ 3 + (97098041088 * X ^ 3 - 3044516751360 * X ^ 4 + 22854387105792 * X ^ 5 + 15994172473344 * X ^ 6 + 293534171136 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-15852775680 * X ^ 3 + 757449149184 * X ^ 4 - 12007758422016 * X ^ 5 + 62260202962944 * X ^ 6 + 14222647885824 * X ^ 7 + 256842399744 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) ^ 2 + (160156984320 * X ^ 3 - 1892698804224 * X ^ 4 - 10713853919232 * X ^ 5 - 50451185664 * X ^ 6 : ℚ⟦X⟧) * G ^ 4 + (-145444014720 * X ^ 3 + 4557151113984 * X ^ 4 - 34131508088832 * X ^ 5 - 24729059524608 * X ^ 6 - 940991053824 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (20759010480 * X ^ 3 - 991105177104 * X ^ 4 + 15687445167360 * X ^ 5 - 80948884930560 * X ^ 6 - 21638908477440 * X ^ 7 - 969529098240 * X ^ 8 - 1358954496 * X ^ 9 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) ^ 2 + (-193048344576 * X ^ 3 + 2299165876224 * X ^ 4 + 12623402631168 * X ^ 5 + 165112971264 * X ^ 6 : ℚ⟦X⟧) * G ^ 5 + (152486102448 * X ^ 3 - 4774154205888 * X ^ 4 + 35670521373696 * X ^ 5 + 26761466658816 * X ^ 6 + 1769111027712 * X ^ 7 + 5888802816 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-18617056200 * X ^ 3 + 887781769560 * X ^ 4 - 14018171713920 * X ^ 5 + 71794061697024 * X ^ 6 + 23566436794368 * X ^ 7 + 1819682537472 * X ^ 8 + 18345885696 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) ^ 2 + (170069789376 * X ^ 3 - 2049312365568 * X ^ 4 - 10729239035904 * X ^ 5 - 314031734784 * X ^ 6 - 566231040 * X ^ 7 : ℚ⟦X⟧) * G ^ 6 + (-114191056692 * X ^ 3 + 3572486097840 * X ^ 4 - 26629193864448 * X ^ 5 - 20628950151168 * X ^ 6 - 2139477442560 * X ^ 7 - 26499612672 * X ^ 8 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (11578014450 * X ^ 3 - 551189369430 * X ^ 4 + 8673778398816 * X ^ 5 - 43949949387264 * X ^ 6 - 18260803067904 * X ^ 7 - 2114363326464 * X ^ 8 - 58095304704 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) ^ 2 + (-110343803904 * X ^ 3 + 1350539785728 * X ^ 4 + 6615543103488 * X ^ 5 + 381186736128 * X ^ 6 + 2548039680 * X ^ 7 : ℚ⟦X⟧) * G ^ 7 + (61083667674 * X ^ 3 - 1909645647552 * X ^ 4 + 14203106782272 * X ^ 5 + 11313824449536 * X ^ 6 + 1709674905600 * X ^ 7 + 50005278720 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-4929508800 * X ^ 3 + 234155076480 * X ^ 4 - 3668113916352 * X ^ 5 + 18319930272000 * X ^ 6 + 9778720481280 * X ^ 7 + 1605158830080 * X ^ 8 + 84651540480 * X ^ 9 + 452984832 * X ^ 10 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) ^ 2 + (52323618276 * X ^ 3 - 652755938976 * X ^ 4 - 2931726431232 * X ^ 5 - 304091615232 * X ^ 6 - 4889051136 * X ^ 7 : ℚ⟦X⟧) * G ^ 8 + (-22873704390 * X ^ 3 + 714611611602 * X ^ 4 - 5304075757344 * X ^ 5 - 4328715932928 * X ^ 6 - 892099325952 * X ^ 7 - 49939808256 * X ^ 8 - 217055232 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (1374894000 * X ^ 3 - 65123319600 * X ^ 4 + 1014275137680 * X ^ 5 - 4971429345168 * X ^ 6 - 3422629479168 * X ^ 7 - 777720434688 * X ^ 8 - 67698229248 * X ^ 9 - 1528823808 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) ^ 2 + (-17678421702 * X ^ 3 + 225399476808 * X ^ 4 + 909384915456 * X ^ 5 + 158058012672 * X ^ 6 + 5319622656 * X ^ 7 + 23592960 * X ^ 8 : ℚ⟦X⟧) * G ^ 9 + (5710224600 * X ^ 3 - 178276055760 * X ^ 4 + 1320524209944 * X ^ 5 + 1103022017856 * X ^ 6 + 289204743168 * X ^ 7 + 27013201920 * X ^ 8 + 488374272 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-226800000 * X ^ 3 + 10704960000 * X ^ 4 - 165527712000 * X ^ 5 + 792232358400 * X ^ 6 + 701722465920 * X ^ 7 + 217397053440 * X ^ 8 + 29448437760 * X ^ 9 + 1486356480 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) ^ 2 + (4037504130 * X ^ 3 - 52692208614 * X ^ 4 - 187317785088 * X ^ 5 - 51112788480 * X ^ 6 - 3423264768 * X ^ 7 - 53084160 * X ^ 8 : ℚ⟦X⟧) * G ^ 10 + (-855198000 * X ^ 3 + 26679553200 * X ^ 4 - 197160460560 * X ^ 5 - 169225768944 * X ^ 6 - 52062061824 * X ^ 7 - 7041945600 * X ^ 8 - 355663872 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (16800000 * X ^ 3 - 789600000 * X ^ 4 + 12102720000 * X ^ 5 - 56231616000 * X ^ 6 - 63716217600 * X ^ 7 - 26499373824 * X ^ 8 - 5402062848 * X ^ 9 - 546373632 * X ^ 10 - 22020096 * X ^ 11 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) ^ 2 + (-559224000 * X ^ 3 + 7471440000 * X ^ 4 + 23036892480 * X ^ 5 + 9229261824 * X ^ 6 + 1170837504 * X ^ 7 + 37158912 * X ^ 8 : ℚ⟦X⟧) * G ^ 11 + (58200000 * X ^ 3 - 1813920000 * X ^ 4 + 13363344000 * X ^ 5 + 11917075200 * X ^ 6 + 3894836160 * X ^ 7 + 589796352 * X ^ 8 + 39469056 * X ^ 9 + 786432 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (35490000 * X ^ 3 - 484722000 * X ^ 4 - 1285462800 * X ^ 5 - 701257200 * X ^ 6 - 151872768 * X ^ 7 - 13787136 * X ^ 8 - 393216 * X ^ 9 : ℚ⟦X⟧) * G ^ 12) * hd1 +
      ((-621084672 * X ^ 3 + 19492503552 * X ^ 4 - 146767085568 * X ^ 5 - 97844723712 * X ^ 6 : ℚ⟦X⟧) + (179159040 * X ^ 3 - 8563802112 * X ^ 4 + 135874215936 * X ^ 5 - 706316599296 * X ^ 6 - 146767085568 * X ^ 7 : ℚ⟦X⟧) * (derivative ℚ G) + (5589762048 * X ^ 3 - 175432531968 * X ^ 4 + 1320903770112 * X ^ 5 + 880602513408 * X ^ 6 : ℚ⟦X⟧) * G + (-1478062080 * X ^ 3 + 70651367424 * X ^ 4 - 1120962281472 * X ^ 5 + 5827111944192 * X ^ 6 + 1210828455936 * X ^ 7 : ℚ⟦X⟧) * G * (derivative ℚ G) + (-23057768448 * X ^ 3 + 723659194368 * X ^ 4 - 5448728051712 * X ^ 5 - 3632485367808 * X ^ 6 : ℚ⟦X⟧) * G ^ 2 + (5541488640 * X ^ 3 - 264863250432 * X ^ 4 + 4201713451008 * X ^ 5 - 21831667679232 * X ^ 6 - 4618067116032 * X ^ 7 - 16307453952 * X ^ 8 : ℚ⟦X⟧) * G ^ 2 * (derivative ℚ G) + (57638117376 * X ^ 3 - 1808852041728 * X ^ 4 + 13617297358848 * X ^ 5 + 9101937475584 * X ^ 6 + 27179089920 * X ^ 7 : ℚ⟦X⟧) * G ^ 3 + (-12459951360 * X ^ 3 + 595406515968 * X ^ 4 - 9441063309312 * X ^ 5 + 48986238025728 * X ^ 6 + 10913508753408 * X ^ 7 + 146767085568 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 * (derivative ℚ G) + (-97232410368 * X ^ 3 + 3050939602944 * X ^ 4 - 22956292767744 * X ^ 5 - 15464435023872 * X ^ 6 - 183458856960 * X ^ 7 : ℚ⟦X⟧) * G ^ 4 + (18664732800 * X ^ 3 - 891502381440 * X ^ 4 + 14123219097600 * X ^ 5 - 73074314280960 * X ^ 6 - 17938836357120 * X ^ 7 - 550376570880 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 * (derivative ℚ G) + (116602301952 * X ^ 3 - 3657531801600 * X ^ 4 + 27492599660544 * X ^ 5 + 18809119309824 * X ^ 6 + 550376570880 * X ^ 7 : ℚ⟦X⟧) * G ^ 5 + (-19553898960 * X ^ 3 + 933266114928 * X ^ 4 - 14762271741696 * X ^ 5 + 76019991478272 * X ^ 6 + 21574570475520 * X ^ 7 + 1174901096448 * X ^ 8 + 4076863488 * X ^ 9 : ℚ⟦X⟧) * G ^ 5 * (derivative ℚ G) + (-101915317152 * X ^ 3 + 3195096357888 * X ^ 4 - 23975880228864 * X ^ 5 - 16825289932800 * X ^ 6 - 962309652480 * X ^ 7 - 2717908992 * X ^ 8 : ℚ⟦X⟧) * G ^ 6 + (14615910540 * X ^ 3 - 696792013092 * X ^ 4 + 10996373868480 * X ^ 5 - 56221104070656 * X ^ 6 - 19241107587072 * X ^ 7 - 1617304485888 * X ^ 8 - 21403533312 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 * (derivative ℚ G) + (65409274224 * X ^ 3 - 2048933232000 * X ^ 4 + 15335764494336 * X ^ 5 + 11170757246976 * X ^ 6 + 1079731814400 * X ^ 7 + 12230590464 * X ^ 8 : ℚ⟦X⟧) * G ^ 7 + (-7792915230 * X ^ 3 + 370921109274 * X ^ 4 - 5834667486816 * X ^ 5 + 29527012145664 * X ^ 6 + 12571428593664 * X ^ 7 + 1515255496704 * X ^ 8 + 45864714240 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 * (derivative ℚ G) + (-30589899237 * X ^ 3 + 957117822696 * X ^ 4 - 7137885390336 * X ^ 5 - 5469335820288 * X ^ 6 - 805499043840 * X ^ 7 - 22932357120 * X ^ 8 : ℚ⟦X⟧) * G ^ 8 + (2903906700 * X ^ 3 - 137921787720 * X ^ 4 + 2160085017708 * X ^ 5 - 10780220347776 * X ^ 6 - 5820027780096 * X ^ 7 - 972646465536 * X ^ 8 - 53169094656 * X ^ 9 - 339738624 * X ^ 10 : ℚ⟦X⟧) * G ^ 8 * (derivative ℚ G) + (10165204620 * X ^ 3 - 317563315236 * X ^ 4 + 2356719530688 * X ^ 5 + 1926977347584 * X ^ 6 + 399232696320 * X ^ 7 + 22698786816 * X ^ 8 + 113246208 * X ^ 9 : ℚ⟦X⟧) * G ^ 9 + (-720090000 * X ^ 3 + 34106346000 * X ^ 4 - 531148330800 * X ^ 5 + 2602649951280 * X ^ 6 + 1797979680000 * X ^ 7 + 410836561920 * X ^ 8 + 36176855040 * X ^ 9 + 849346560 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 * (derivative ℚ G) + (-2278076400 * X ^ 3 + 71024545440 * X ^ 4 - 523723852656 * X ^ 5 - 463732335360 * X ^ 6 - 126725160960 * X ^ 7 - 12373917696 * X ^ 8 - 254803968 * X ^ 9 : ℚ⟦X⟧) * G ^ 10 + (106920000 * X ^ 3 - 5046624000 * X ^ 4 + 78034492800 * X ^ 5 - 373480968960 * X ^ 6 - 330812019648 * X ^ 7 - 102487182336 * X ^ 8 - 13882834944 * X ^ 9 - 700710912 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 * (derivative ℚ G) + (309096000 * X ^ 3 - 9612302400 * X ^ 4 + 70301027520 * X ^ 5 + 68400168768 * X ^ 6 + 23391452160 * X ^ 7 + 3475685376 * X ^ 8 + 191102976 * X ^ 9 : ℚ⟦X⟧) * G ^ 11 + (-7200000 * X ^ 3 + 338400000 * X ^ 4 - 5186880000 * X ^ 5 + 24099264000 * X ^ 6 + 27306950400 * X ^ 7 + 11356874496 * X ^ 8 + 2315169792 * X ^ 9 + 234160128 * X ^ 10 + 9437184 * X ^ 11 : ℚ⟦X⟧) * G ^ 11 * (derivative ℚ G) + (-19200000 * X ^ 3 + 595200000 * X ^ 4 - 4308480000 * X ^ 5 - 4670976000 * X ^ 6 - 1917081600 * X ^ 7 - 388306944 * X ^ 8 - 39124992 * X ^ 9 - 1572864 * X ^ 10 : ℚ⟦X⟧) * G ^ 12) * hd2 +
      ((26542080 * X ^ 3 - 1268711424 * X ^ 4 + 20129513472 * X ^ 5 - 104639496192 * X ^ 6 - 21743271936 * X ^ 7 : ℚ⟦X⟧) + (-238878720 * X ^ 3 + 11418402816 * X ^ 4 - 181165621248 * X ^ 5 + 941755465728 * X ^ 6 + 195689447424 * X ^ 7 : ℚ⟦X⟧) * G + (985374720 * X ^ 3 - 47100911616 * X ^ 4 + 747308187648 * X ^ 5 - 3884741296128 * X ^ 6 - 807218970624 * X ^ 7 : ℚ⟦X⟧) * G ^ 2 + (-2462883840 * X ^ 3 + 117717000192 * X ^ 4 - 1867428200448 * X ^ 5 + 9702963412992 * X ^ 6 + 2052474273792 * X ^ 7 + 7247757312 * X ^ 8 : ℚ⟦X⟧) * G ^ 3 + (4153317120 * X ^ 3 - 198468838656 * X ^ 4 + 3147021103104 * X ^ 5 - 16328746008576 * X ^ 6 - 3637836251136 * X ^ 7 - 48922361856 * X ^ 8 : ℚ⟦X⟧) * G ^ 4 + (-4977262080 * X ^ 3 + 237733968384 * X ^ 4 - 3766191759360 * X ^ 5 + 19486483808256 * X ^ 6 + 4783689695232 * X ^ 7 + 146767085568 * X ^ 8 : ℚ⟦X⟧) * G ^ 5 + (4345310880 * X ^ 3 - 207392469984 * X ^ 4 + 3280504831488 * X ^ 5 - 16893331439616 * X ^ 6 - 4794348994560 * X ^ 7 - 261089132544 * X ^ 8 - 905969664 * X ^ 9 : ℚ⟦X⟧) * G ^ 6 + (-2783982960 * X ^ 3 + 132722288208 * X ^ 4 - 2094547403520 * X ^ 5 + 10708781727744 * X ^ 6 + 3664972873728 * X ^ 7 + 308057997312 * X ^ 8 + 4076863488 * X ^ 9 : ℚ⟦X⟧) * G ^ 7 + (1298819205 * X ^ 3 - 61820184879 * X ^ 4 + 972444581136 * X ^ 5 - 4921168690944 * X ^ 6 - 2095238098944 * X ^ 7 - 252542582784 * X ^ 8 - 7644119040 * X ^ 9 : ℚ⟦X⟧) * G ^ 8 + (-430208400 * X ^ 3 + 20432857440 * X ^ 4 - 320012595216 * X ^ 5 + 1597069681152 * X ^ 6 + 862226337792 * X ^ 7 + 144095772672 * X ^ 8 + 7876902912 * X ^ 9 + 50331648 * X ^ 10 : ℚ⟦X⟧) * G ^ 9 + (96012000 * X ^ 3 - 4547512800 * X ^ 4 + 70819777440 * X ^ 5 - 347019993504 * X ^ 6 - 239730624000 * X ^ 7 - 54778208256 * X ^ 8 - 4823580672 * X ^ 9 - 113246208 * X ^ 10 : ℚ⟦X⟧) * G ^ 10 + (-12960000 * X ^ 3 + 611712000 * X ^ 4 - 9458726400 * X ^ 5 + 45270420480 * X ^ 6 + 40098426624 * X ^ 7 + 12422688768 * X ^ 8 + 1682767872 * X ^ 9 + 84934656 * X ^ 10 : ℚ⟦X⟧) * G ^ 11 + (800000 * X ^ 3 - 37600000 * X ^ 4 + 576320000 * X ^ 5 - 2677696000 * X ^ 6 - 3034105600 * X ^ 7 - 1261874944 * X ^ 8 - 257241088 * X ^ 9 - 26017792 * X ^ 10 - 1048576 * X ^ 11 : ℚ⟦X⟧) * G ^ 12) * hd3
  have k20 : constantCoeff (20 : ℚ⟦X⟧) = 20 := cnum 20
  have k48 : constantCoeff (48 : ℚ⟦X⟧) = 48 := cnum 48
  have k81 : constantCoeff (81 : ℚ⟦X⟧) = 81 := cnum 81
  have k108 : constantCoeff (108 : ℚ⟦X⟧) = 108 := cnum 108
  have hPG : (-48 : ℚ⟦X⟧) + (108 : ℚ⟦X⟧) * G + (-81 : ℚ⟦X⟧) * G ^ 2 + (20 + 4 * X : ℚ⟦X⟧) * G ^ 3 ≠ 0 := by
    intro h
    have h' := congrArg constantCoeff h
    simp [h0, k20, k48, k81, k108] at h'
    norm_num at h'
  have h2 := (mul_eq_zero.mp hfull).resolve_left (pow_ne_zero 5 hPG)
  linear_combination h2

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem keyC (G : ℚ⟦X⟧)
    (hP : (16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G ^ 2 + (-27 : ℚ⟦X⟧) * G ^ 3 + (5 + X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * C 5 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * C (-239) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * C 3792 + derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * C (-19712) +
      derivative ℚ (derivative ℚ (derivative ℚ G)) * X * X * X * X * X * X * X * C (-4096) + derivative ℚ (derivative ℚ G) * X * X * X * C (-117) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * C 3672 + derivative ℚ (derivative ℚ G) * X * X * X * X * X * C (-27648) +
      derivative ℚ (derivative ℚ G) * X * X * X * X * X * X * C (-18432) + derivative ℚ G * X * X * X * C 192 +
      derivative ℚ G * X * X * X * X * C (-2256) + derivative ℚ G * X * X * X * X * X * C (-13056) +
      G * X * X * X * C 1968 + G * X * X * X * X * C (-384) =
      C 2592 * X * X * X := by
  have h := key G hP h0
  simp only [map_ofNat, map_neg]
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem rel (G : ℚ⟦X⟧)
    (hP : (16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G ^ 2 + (-27 : ℚ⟦X⟧) * G ^ 3 + (5 + X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) (m : ℕ) :
    5 * ((m : ℚ) + 7) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1) G + (-239) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      3792 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-19712) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1 + 1) G +
      (-4096) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * ((m : ℚ) + 1) * coeff (m + 1 + 1 + 1) G + (-117) * ((m : ℚ) + 6) * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1 + 1) G +
      3672 * ((m : ℚ) + 5) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1 + 1) G + (-27648) * ((m : ℚ) + 4) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1 + 1) G +
      (-18432) * ((m : ℚ) + 3) * ((m : ℚ) + 2) * coeff (m + 1 + 1 + 1) G + 192 * ((m : ℚ) + 5) * coeff (m + 1 + 1 + 1 + 1 + 1) G +
      (-2256) * ((m : ℚ) + 4) * coeff (m + 1 + 1 + 1 + 1) G + (-13056) * ((m : ℚ) + 3) * coeff (m + 1 + 1 + 1) G +
      1968 * coeff (m + 1 + 1 + 1 + 1) G + (-384) * coeff (m + 1 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (m + 1 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE0 (G : ℚ⟦X⟧)
    (hP : (16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G ^ 2 + (-27 : ℚ⟦X⟧) * G ^ 3 + (5 + X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    120 * coeff (0 + 1 + 1 + 1 + 1) G + (-1434) * coeff (0 + 1 + 1 + 1) G +
      (-702) * coeff (0 + 1 + 1 + 1) G + 7344 * coeff (0 + 1 + 1) G +
      384 * coeff (0 + 1 + 1) G + (-2256) * coeff (0 + 1) G +
      1968 * coeff (0 + 1) G + (-384) * coeff (0) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE1 (G : ℚ⟦X⟧)
    (hP : (16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G ^ 2 + (-27 : ℚ⟦X⟧) * G ^ 3 + (5 + X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    300 * coeff (0 + 1 + 1 + 1 + 1 + 1) G + (-5736) * coeff (0 + 1 + 1 + 1 + 1) G +
      22752 * coeff (0 + 1 + 1 + 1) G + (-1404) * coeff (0 + 1 + 1 + 1 + 1) G +
      22032 * coeff (0 + 1 + 1 + 1) G + (-55296) * coeff (0 + 1 + 1) G +
      576 * coeff (0 + 1 + 1 + 1) G + (-4512) * coeff (0 + 1 + 1) G +
      (-13056) * coeff (0 + 1) G + 1968 * coeff (0 + 1 + 1) G +
      (-384) * coeff (0 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem relE2 (G : ℚ⟦X⟧)
    (hP : (16 : ℚ⟦X⟧) + (-48 : ℚ⟦X⟧) * G + (54 : ℚ⟦X⟧) * G ^ 2 + (-27 : ℚ⟦X⟧) * G ^ 3 + (5 + X : ℚ⟦X⟧) * G ^ 4 = 0)
    (h0 : constantCoeff G = (1 : ℚ)) :
    600 * coeff (0 + 1 + 1 + 1 + 1 + 1 + 1) G + (-14340) * coeff (0 + 1 + 1 + 1 + 1 + 1) G +
      91008 * coeff (0 + 1 + 1 + 1 + 1) G + (-118272) * coeff (0 + 1 + 1 + 1) G +
      (-2340) * coeff (0 + 1 + 1 + 1 + 1 + 1) G + 44064 * coeff (0 + 1 + 1 + 1 + 1) G +
      (-165888) * coeff (0 + 1 + 1 + 1) G + (-36864) * coeff (0 + 1 + 1) G +
      768 * coeff (0 + 1 + 1 + 1 + 1) G + (-6768) * coeff (0 + 1 + 1 + 1) G +
      (-26112) * coeff (0 + 1 + 1) G + 1968 * coeff (0 + 1 + 1 + 1) G +
      (-384) * coeff (0 + 1 + 1) G = 0 := by
  have h := congrArg (coeff (0 + 1 + 1 + 1 + 1 + 1 + 1)) (keyC G hP h0)
  simp only [map_add, PowerSeries.coeff_mul_C, PowerSeries.coeff_succ_mul_X, coeff_derivative,
    PowerSeries.coeff_C, Nat.add_one_ne_zero, ↓reduceIte, PowerSeries.coeff_zero_mul_X] at h
  push_cast at h
  linear_combination h

end A025757Aux

set_option maxRecDepth 20000 in
set_option maxHeartbeats 4000000 in
theorem OMA.solution : type_of% @OMA.S_oeis_a025757.main := by
  intro T G hT hT0 hG n hn
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 + 1 + 1 + 1 := ⟨n - 4, by omega⟩
  have e1 : m + 1 + 1 + 1 + 1 - 1 = m + 1 + 1 + 1 := rfl
  have e2 : m + 1 + 1 + 1 + 1 - 2 = m + 1 + 1 := rfl
  have e3 : m + 1 + 1 + 1 + 1 - 3 = m + 1 := rfl
  have e4 : m + 1 + 1 + 1 + 1 - 4 = m := rfl
  rw [e1, e2, e3, e4]
  have hT0c : PowerSeries.constantCoeff T = 1 := by simpa using hT0
  have kn3 : PowerSeries.constantCoeff (3 : PowerSeries ℚ) = 3 := A025757Aux.cnum 3
  have hN1 : ((3) + (1) * T : PowerSeries ℚ) ≠ 0 := by
    intro h
    have h' := congrArg PowerSeries.constantCoeff h
    simp [hT0c, kn3] at h'
    norm_num at h'
  have hM : ((3) + (1) * T) ^ 4 * ((16 : PowerSeries ℚ) + (-48 : PowerSeries ℚ) * G + (54 : PowerSeries ℚ) * G ^ 2 + (-27 : PowerSeries ℚ) * G ^ 3 + (5 + PowerSeries.X : PowerSeries ℚ) * G ^ 4) = 0 := by
    linear_combination ((16)) * hT +
      ((-328) + (-432) * T + (-216) * T ^ 2 + (-48) * T ^ 3 + (726) * G + (890) * G * T + (378) * G * T ^ 2 + (54) * G * T ^ 3 + (-549) * G ^ 2 + (-609) * G ^ 2 * T + (-223) * G ^ 2 * T ^ 2 + (-27) * G ^ 2 * T ^ 3 + (135) * G ^ 3 + (135) * G ^ 3 * T + (45) * G ^ 3 * T ^ 2 + (5) * G ^ 3 * T ^ 3 + (64) * PowerSeries.X + (48) * PowerSeries.X * G + (16) * PowerSeries.X * G * T + (36) * PowerSeries.X * G ^ 2 + (24) * PowerSeries.X * G ^ 2 * T + (4) * PowerSeries.X * G ^ 2 * T ^ 2 + (27) * PowerSeries.X * G ^ 3 + (27) * PowerSeries.X * G ^ 3 * T + (9) * PowerSeries.X * G ^ 3 * T ^ 2 + (1) * PowerSeries.X * G ^ 3 * T ^ 3) * hG
  have hP : (16 : PowerSeries ℚ) + (-48 : PowerSeries ℚ) * G + (54 : PowerSeries ℚ) * G ^ 2 + (-27 : PowerSeries ℚ) * G ^ 3 + (5 + PowerSeries.X : PowerSeries ℚ) * G ^ 4 = 0 := (mul_eq_zero.mp hM).resolve_left (pow_ne_zero 4 hN1)
  have h0c : PowerSeries.constantCoeff G = (1 : ℚ) := by
    have h := congrArg PowerSeries.constantCoeff hG
    have k3 : PowerSeries.constantCoeff (3 : PowerSeries ℚ) = 3 := A025757Aux.cnum 3
    have k4 : PowerSeries.constantCoeff (4 : PowerSeries ℚ) = 4 := A025757Aux.cnum 4
    simp only [map_mul, map_add, hT0c, k3, k4] at h
    linarith
  cases m with
  | zero =>
    have r := A025757Aux.relE0 G hP h0c
    push_cast
    linear_combination r
  | succ m =>
    cases m with
    | zero =>
      have r := A025757Aux.relE1 G hP h0c
      push_cast
      linear_combination r
    | succ m =>
      cases m with
      | zero =>
        have r := A025757Aux.relE2 G hP h0c
        push_cast
        linear_combination r
      | succ m =>
        have r := A025757Aux.rel G hP h0c m
        push_cast
        linear_combination r
