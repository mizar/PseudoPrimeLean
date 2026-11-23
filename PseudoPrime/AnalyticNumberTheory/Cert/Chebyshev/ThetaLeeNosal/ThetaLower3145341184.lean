/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3145341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3113341184 :
    ThetaLowerSegment 3113341184 3113472256 (77831487911313 / 25000) (155669435142351 / 50000) := by
  exact
    packedTile65536 3113341184 3113472256 14 5910 55797 32 _ _ (437179 / 20000) (1092949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113472256 :
    ThetaLowerSegment 3113472256 3113603328 (155669435142351 / 50000) (19459499924631 / 6250) := by
  exact
    packedTile65536 3113472256 3113603328 14 6006 55798 32 _ _ (2185899 / 100000) (1092951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113603328 :
    ThetaLowerSegment 3113603328 3113734400 (19459499924631 / 6250) (311365138257029 / 100000) := by
  exact
    packedTile65536 3113603328 3113734400 14 6011 55799 32 _ _ (2185903 / 100000) (1092953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113734400 :
    ThetaLowerSegment 3113734400 3113865472 (311365138257029 / 100000)
      (311378100685539 / 100000) := by
  exact
    packedTile65536 3113734400 3113865472 14 5930 55800 32 _ _ (2185907 / 100000) (218591 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113865472 :
    ThetaLowerSegment 3113865472 3113996544 (311378100685539 / 100000)
      (311391144022443 / 100000) := by
  exact
    packedTile65536 3113865472 3113996544 14 5967 55802 32 _ _ (273239 / 12500) (437183 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3113996544 :
    ThetaLowerSegment 3113996544 3114127616 (311391144022443 / 100000)
      (311404290121267 / 100000) := by
  exact
    packedTile65536 3113996544 3114127616 14 6014 55803 32 _ _ (546479 / 25000) (2185919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114127616 :
    ThetaLowerSegment 3114127616 3114258688 (311404290121267 / 100000)
      (311417320390387 / 100000) := by
  exact
    packedTile65536 3114127616 3114258688 14 5961 55804 32 _ _ (13662 / 625) (2185923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114258688 :
    ThetaLowerSegment 3114258688 3114389760 (311417320390387 / 100000)
      (311430361612971 / 100000) := by
  exact
    packedTile65536 3114258688 3114389760 14 5966 55805 32 _ _ (546481 / 25000) (2185927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114389760 :
    ThetaLowerSegment 3114389760 3114520832 (311430361612971 / 100000)
      (311443564618091 / 100000) := by
  exact
    packedTile65536 3114389760 3114520832 14 6040 55806 32 _ _ (273241 / 12500) (2185931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114520832 :
    ThetaLowerSegment 3114520832 3114651904 (311443564618091 / 100000)
      (311456780769009 / 100000) := by
  exact
    packedTile65536 3114520832 3114651904 14 6046 55807 32 _ _ (2185933 / 100000) (136621 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114651904 :
    ThetaLowerSegment 3114651904 3114782976 (311456780769009 / 100000)
      (31147001224567 / 10000) := by
  exact
    packedTile65536 3114651904 3114782976 14 6053 55809 32 _ _ (2185937 / 100000) (109297 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114782976 :
    ThetaLowerSegment 3114782976 3114914048 (31147001224567 / 10000) (77870793995593 / 25000) := by
  exact
    packedTile65536 3114782976 3114914048 14 6022 55810 32 _ _ (2185941 / 100000) (273243 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3114914048 :
    ThetaLowerSegment 3114914048 3115045120 (77870793995593 / 25000)
      (311496385648007 / 100000) := by
  exact
    packedTile65536 3114914048 3115045120 14 6043 55811 32 _ _ (437189 / 20000) (546487 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115045120 :
    ThetaLowerSegment 3115045120 3115176192 (311496385648007 / 100000)
      (311509326466087 / 100000) := by
  exact
    packedTile65536 3115045120 3115176192 14 5920 55812 32 _ _ (2185949 / 100000) (68311 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115176192 :
    ThetaLowerSegment 3115176192 3115307264 (311509326466087 / 100000)
      (311522455305811 / 100000) := by
  exact
    packedTile65536 3115176192 3115307264 14 6006 55813 32 _ _ (1092977 / 50000) (2185957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115307264 :
    ThetaLowerSegment 3115307264 3115438336 (311522455305811 / 100000)
      (311535660678089 / 100000) := by
  exact
    packedTile65536 3115307264 3115438336 14 6041 55814 32 _ _ (1092979 / 50000) (2185961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115438336 :
    ThetaLowerSegment 3115438336 3115569408 (311535660678089 / 100000)
      (311548787379899 / 100000) := by
  exact
    packedTile65536 3115438336 3115569408 14 6005 55816 32 _ _ (1092981 / 50000) (437193 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115569408 :
    ThetaLowerSegment 3115569408 3115700480 (311548787379899 / 100000)
      (62312365770611 / 20000) := by
  exact
    packedTile65536 3115569408 3115700480 14 5966 55817 32 _ _ (1092983 / 50000) (2185969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115700480 :
    ThetaLowerSegment 3115700480 3115831552 (62312365770611 / 20000) (62314954833479 / 20000) := by
  exact
    packedTile65536 3115700480 3115831552 14 5922 55818 32 _ _ (218597 / 10000) (2185973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115831552 :
    ThetaLowerSegment 3115831552 3115962624 (62314954833479 / 20000) (62317577129089 / 20000) := by
  exact
    packedTile65536 3115831552 3115962624 14 5998 55819 32 _ _ (87439 / 4000) (1092989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3115962624 :
    ThetaLowerSegment 3115962624 3116093696 (62317577129089 / 20000) (77900261856251 / 25000) := by
  exact
    packedTile65536 3115962624 3116093696 14 6021 55820 32 _ _ (2185979 / 100000) (1092991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3116093696 :
    ThetaLowerSegment 3116093696 3116224768 (77900261856251 / 25000)
      (311614130533259 / 100000) := by
  exact
    packedTile65536 3116093696 3116224768 14 5985 55821 32 _ _ (2185983 / 100000) (1092993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3116224768 :
    ThetaLowerSegment 3116224768 3116355840 (311614130533259 / 100000)
      (155813685528259 / 50000) := by
  exact
    packedTile65536 3116224768 3116355840 14 6057 55823 32 _ _ (2185987 / 100000) (218599 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3116355840 :
    ThetaLowerSegment 3116355840 3116486912 (155813685528259 / 50000)
      (155820245690251 / 50000) := by
  exact
    packedTile65536 3116355840 3116486912 14 6002 55824 32 _ _ (273249 / 12500) (437199 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3116486912 :
    ThetaLowerSegment 3116486912 3116617984 (155820245690251 / 50000)
      (155826737005373 / 50000) := by
  exact
    packedTile65536 3116486912 3116617984 14 5939 55825 32 _ _ (546499 / 25000) (2185999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3116617984 :
    ThetaLowerSegment 3116617984 3116749056 (155826737005373 / 50000)
      (155833264401373 / 50000) := by
  exact
    packedTile65536 3116617984 3116749056 14 5972 55826 32 _ _ (1093 / 50) (2186003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3116749056 :
    ThetaLowerSegment 3116749056 3116880128 (155833264401373 / 50000)
      (155839781972299 / 50000) := by
  exact
    packedTile65536 3116749056 3116880128 14 5963 55827 32 _ _ (546501 / 25000) (2186007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3116880128 :
    ThetaLowerSegment 3116880128 3117011200 (155839781972299 / 50000)
      (155846249276967 / 50000) := by
  exact
    packedTile65536 3116880128 3117011200 14 5917 55829 32 _ _ (273251 / 12500) (2186011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117011200 :
    ThetaLowerSegment 3117011200 3117142272 (155846249276967 / 50000)
      (155852899128513 / 50000) := by
  exact
    packedTile65536 3117011200 3117142272 14 6084 55830 32 _ _ (2186013 / 100000) (68313 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117142272 :
    ThetaLowerSegment 3117142272 3117273344 (155852899128513 / 50000)
      (311719008357757 / 100000) := by
  exact
    packedTile65536 3117142272 3117273344 14 6043 55831 32 _ _ (2186017 / 100000) (109301 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117273344 :
    ThetaLowerSegment 3117273344 3117404416 (311719008357757 / 100000)
      (311731932113909 / 100000) := by
  exact
    packedTile65536 3117273344 3117404416 14 5912 55832 32 _ _ (2186021 / 100000) (273253 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117404416 :
    ThetaLowerSegment 3117404416 3117535488 (311731932113909 / 100000)
      (311744930218559 / 100000) := by
  exact
    packedTile65536 3117404416 3117535488 14 5946 55833 32 _ _ (87441 / 4000) (546507 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117535488 :
    ThetaLowerSegment 3117535488 3117666560 (311744930218559 / 100000)
      (77939529632879 / 25000) := by
  exact
    packedTile65536 3117535488 3117666560 14 6033 55834 32 _ _ (2186029 / 100000) (136627 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117666560 :
    ThetaLowerSegment 3117666560 3117797632 (77939529632879 / 25000) (77942865520763 / 25000) := by
  exact
    packedTile65536 3117666560 3117797632 14 6104 55836 32 _ _ (1093017 / 50000) (2186037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117797632 :
    ThetaLowerSegment 3117797632 3117928704 (77942865520763 / 25000) (77946159880029 / 25000) := by
  exact
    packedTile65536 3117797632 3117928704 14 6028 55837 32 _ _ (1093019 / 50000) (2186041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3117928704 :
    ThetaLowerSegment 3117928704 3118059776 (77946159880029 / 25000) (155898865862827 / 50000) := by
  exact
    packedTile65536 3117928704 3118059776 14 5989 55838 32 _ _ (1093021 / 50000) (437209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118059776 :
    ThetaLowerSegment 3118059776 3118190848 (155898865862827 / 50000)
      (155905393396183 / 50000) := by
  exact
    packedTile65536 3118059776 3118190848 14 5972 55839 32 _ _ (1093023 / 50000) (2186049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118190848 :
    ThetaLowerSegment 3118190848 3118321920 (155905393396183 / 50000)
      (155911997453233 / 50000) := by
  exact
    packedTile65536 3118190848 3118321920 14 6042 55840 32 _ _ (43721 / 2000) (2186053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118321920 :
    ThetaLowerSegment 3118321920 3118452992 (155911997453233 / 50000)
      (311837091561971 / 100000) := by
  exact
    packedTile65536 3118321920 3118452992 14 5991 55841 32 _ _ (437211 / 20000) (1093029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118452992 :
    ThetaLowerSegment 3118452992 3118584064 (311837091561971 / 100000)
      (311850234148679 / 100000) := by
  exact
    packedTile65536 3118452992 3118584064 14 6012 55843 32 _ _ (2186059 / 100000) (1093031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118584064 :
    ThetaLowerSegment 3118584064 3118715136 (311850234148679 / 100000) (12474537693653 / 4000) := by
  exact
    packedTile65536 3118584064 3118715136 14 6042 55844 32 _ _ (2186063 / 100000) (1093033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118715136 :
    ThetaLowerSegment 3118715136 3118846208 (12474537693653 / 4000) (12475066721867 / 4000) := by
  exact
    packedTile65536 3118715136 3118846208 14 6050 55845 32 _ _ (2186067 / 100000) (218607 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118846208 :
    ThetaLowerSegment 3118846208 3118977280 (12475066721867 / 4000) (15594482118903 / 5000) := by
  exact
    packedTile65536 3118846208 3118977280 14 5935 55846 32 _ _ (2186071 / 100000) (1093037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3118977280 :
    ThetaLowerSegment 3118977280 3119108352 (15594482118903 / 5000) (7797569244111 / 2500) := by
  exact
    packedTile65536 3118977280 3119108352 14 6005 55847 32 _ _ (546519 / 25000) (2186079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3119108352 :
    ThetaLowerSegment 3119108352 3119239424 (7797569244111 / 2500) (7797897921239 / 2500) := by
  exact
    packedTile65536 3119108352 3119239424 14 6014 55848 32 _ _ (13663 / 625) (2186083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3119239424 :
    ThetaLowerSegment 3119239424 3119370496 (7797897921239 / 2500) (38991106215313 / 12500) := by
  exact
    packedTile65536 3119239424 3119370496 14 5916 55850 32 _ _ (546521 / 25000) (2186087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3119370496 :
    ThetaLowerSegment 3119370496 3119501568 (38991106215313 / 12500) (38992752339577 / 12500) := by
  exact
    packedTile65536 3119370496 3119501568 14 6024 55851 32 _ _ (273261 / 12500) (2186091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3119501568 :
    ThetaLowerSegment 3119501568 3119632640 (38992752339577 / 12500) (9748601939436 / 3125) := by
  exact
    packedTile65536 3119501568 3119632640 14 6058 55852 32 _ _ (546523 / 25000) (437219 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3119632640 :
    ThetaLowerSegment 3119632640 3119763712 (9748601939436 / 3125) (155984261463177 / 50000) := by
  exact
    packedTile65536 3119632640 3119763712 14 6066 55853 32 _ _ (2186097 / 100000) (21861 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3119763712 :
    ThetaLowerSegment 3119763712 3119894784 (155984261463177 / 50000)
      (311981611113041 / 100000) := by
  exact
    packedTile65536 3119763712 3119894784 14 5987 55854 32 _ _ (2186101 / 100000) (273263 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3119894784 :
    ThetaLowerSegment 3119894784 3120025856 (311981611113041 / 100000)
      (77998648597659 / 25000) := by
  exact
    packedTile65536 3119894784 3120025856 14 5939 55856 32 _ _ (437221 / 20000) (546527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120025856 :
    ThetaLowerSegment 3120025856 3120156928 (77998648597659 / 25000) (78001923388941 / 25000) := by
  exact
    packedTile65536 3120025856 3120156928 14 5992 55857 32 _ _ (2186109 / 100000) (68316 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120156928 :
    ThetaLowerSegment 3120156928 3120288000 (78001923388941 / 25000) (19501293534743 / 6250) := by
  exact
    packedTile65536 3120156928 3120288000 14 5948 55858 32 _ _ (2186113 / 100000) (546529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120288000 :
    ThetaLowerSegment 3120288000 3120419072 (19501293534743 / 6250) (156016951447363 / 50000) := by
  exact
    packedTile65536 3120288000 3120419072 14 6041 55859 32 _ _ (1093059 / 50000) (2186121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120419072 :
    ThetaLowerSegment 3120419072 3120550144 (156016951447363 / 50000) (39005870075179 / 12500) := by
  exact
    packedTile65536 3120419072 3120550144 14 5973 55860 32 _ _ (1093061 / 50000) (17489 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120550144 :
    ThetaLowerSegment 3120550144 3120681216 (39005870075179 / 12500) (78014994198909 / 25000) := by
  exact
    packedTile65536 3120550144 3120681216 14 5954 55861 32 _ _ (1093063 / 50000) (2186129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120681216 :
    ThetaLowerSegment 3120681216 3120812288 (78014994198909 / 25000) (78018282138429 / 25000) := by
  exact
    packedTile65536 3120681216 3120812288 14 6016 55863 32 _ _ (218613 / 10000) (2186133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120812288 :
    ThetaLowerSegment 3120812288 3120943360 (78018282138429 / 25000) (156043154377801 / 50000) := by
  exact
    packedTile65536 3120812288 3120943360 14 6029 55864 32 _ _ (1093067 / 50000) (2186137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3120943360 :
    ThetaLowerSegment 3120943360 3121074432 (156043154377801 / 50000) (62419896923071 / 20000) := by
  exact
    packedTile65536 3120943360 3121074432 14 6027 55865 32 _ _ (2186139 / 100000) (1093071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121074432 :
    ThetaLowerSegment 3121074432 3121205504 (62419896923071 / 20000) (156056297457463 / 50000) := by
  exact
    packedTile65536 3121074432 3121205504 14 5997 55866 32 _ _ (2186143 / 100000) (1093073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121205504 :
    ThetaLowerSegment 3121205504 3121336576 (156056297457463 / 50000) (31212560686187 / 10000) := by
  exact
    packedTile65536 3121205504 3121336576 14 5952 55867 32 _ _ (2186147 / 100000) (43723 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121336576 :
    ThetaLowerSegment 3121336576 3121467648 (31212560686187 / 10000) (78034703896553 / 25000) := by
  exact
    packedTile65536 3121336576 3121467648 14 6042 55868 32 _ _ (2186151 / 100000) (1093077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121467648 :
    ThetaLowerSegment 3121467648 3121598720 (78034703896553 / 25000)
      (312151856000787 / 100000) := by
  exact
    packedTile65536 3121467648 3121598720 14 5965 55870 32 _ _ (437231 / 20000) (1093079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121598720 :
    ThetaLowerSegment 3121598720 3121729792 (312151856000787 / 100000)
      (312164957657667 / 100000) := by
  exact
    packedTile65536 3121598720 3121729792 14 5993 55871 32 _ _ (27327 / 1250) (2186163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121729792 :
    ThetaLowerSegment 3121729792 3121860864 (312164957657667 / 100000)
      (312178039663043 / 100000) := by
  exact
    packedTile65536 3121729792 3121860864 14 5984 55872 32 _ _ (546541 / 25000) (2186167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121860864 :
    ThetaLowerSegment 3121860864 3121991936 (312178039663043 / 100000)
      (312191196022067 / 100000) := by
  exact
    packedTile65536 3121860864 3121991936 14 6018 55873 32 _ _ (273271 / 12500) (2186171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3121991936 :
    ThetaLowerSegment 3121991936 3122123008 (312191196022067 / 100000)
      (62440838125687 / 20000) := by
  exact
    packedTile65536 3121991936 3122123008 14 5944 55874 32 _ _ (546543 / 25000) (87447 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3122123008 :
    ThetaLowerSegment 3122123008 3122254080 (62440838125687 / 20000)
      (312217279264147 / 100000) := by
  exact
    packedTile65536 3122123008 3122254080 14 5987 55875 32 _ _ (68318 / 3125) (2186179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3122254080 :
    ThetaLowerSegment 3122254080 3122385152 (312217279264147 / 100000)
      (39028804189403 / 12500) := by
  exact
    packedTile65536 3122254080 3122385152 14 6017 55877 32 _ _ (2186181 / 100000) (273273 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3122385152 :
    ThetaLowerSegment 3122385152 3122516224 (39028804189403 / 12500) (156121834339607 / 50000) := by
  exact
    packedTile65536 3122385152 3122516224 14 6054 55878 32 _ _ (437237 / 20000) (546547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3122516224 :
    ThetaLowerSegment 3122516224 3122647296 (156121834339607 / 50000)
      (312256836095561 / 100000) := by
  exact
    packedTile65536 3122516224 3122647296 14 6023 55879 32 _ _ (2186189 / 100000) (136637 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3122647296 :
    ThetaLowerSegment 3122647296 3122778368 (312256836095561 / 100000)
      (312269835199139 / 100000) := by
  exact
    packedTile65536 3122647296 3122778368 14 5946 55880 32 _ _ (2186193 / 100000) (546549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3122778368 :
    ThetaLowerSegment 3122778368 3122909440 (312269835199139 / 100000)
      (312282869305653 / 100000) := by
  exact
    packedTile65536 3122778368 3122909440 14 5962 55881 32 _ _ (2186197 / 100000) (10931 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3122909440 :
    ThetaLowerSegment 3122909440 3123040512 (312282869305653 / 100000)
      (62459204299377 / 20000) := by
  exact
    packedTile65536 3122909440 3123040512 14 6016 55882 32 _ _ (1093101 / 50000) (437241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123040512 :
    ThetaLowerSegment 3123040512 3123171584 (62459204299377 / 20000)
      (312309077519117 / 100000) := by
  exact
    packedTile65536 3123040512 3123171584 14 5972 55884 32 _ _ (1093103 / 50000) (2186209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123171584 :
    ThetaLowerSegment 3123171584 3123302656 (312309077519117 / 100000)
      (312322186034277 / 100000) := by
  exact
    packedTile65536 3123171584 3123302656 14 5996 55885 32 _ _ (218621 / 10000) (2186213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123302656 :
    ThetaLowerSegment 3123302656 3123433728 (312322186034277 / 100000)
      (62467070282997 / 20000) := by
  exact
    packedTile65536 3123302656 3123433728 14 6022 55886 32 _ _ (1093107 / 50000) (2186217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123433728 :
    ThetaLowerSegment 3123433728 3123564800 (62467070282997 / 20000)
      (312348602082283 / 100000) := by
  exact
    packedTile65536 3123433728 3123564800 14 6061 55887 32 _ _ (1093109 / 50000) (2186221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123564800 :
    ThetaLowerSegment 3123564800 3123695872 (312348602082283 / 100000)
      (312361802496757 / 100000) := by
  exact
    packedTile65536 3123564800 3123695872 14 6038 55888 32 _ _ (2186223 / 100000) (1093113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123695872 :
    ThetaLowerSegment 3123695872 3123826944 (312361802496757 / 100000)
      (312374880506671 / 100000) := by
  exact
    packedTile65536 3123695872 3123826944 14 5982 55890 32 _ _ (2186227 / 100000) (218623 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123826944 :
    ThetaLowerSegment 3123826944 3123958016 (312374880506671 / 100000)
      (312388102831759 / 100000) := by
  exact
    packedTile65536 3123826944 3123958016 14 6048 55891 32 _ _ (2186231 / 100000) (1093117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3123958016 :
    ThetaLowerSegment 3123958016 3124089088 (312388102831759 / 100000)
      (156200628703877 / 50000) := by
  exact
    packedTile65536 3123958016 3124089088 14 6017 55892 32 _ _ (437247 / 20000) (1093119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3124089088 :
    ThetaLowerSegment 3124089088 3124220160 (156200628703877 / 50000)
      (156207270497959 / 50000) := by
  exact
    packedTile65536 3124089088 3124220160 14 6076 55893 32 _ _ (2186239 / 100000) (1093121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3124220160 :
    ThetaLowerSegment 3124220160 3124351232 (156207270497959 / 50000)
      (156213847813033 / 50000) := by
  exact
    packedTile65536 3124220160 3124351232 14 6017 55894 32 _ _ (546561 / 25000) (2186247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3124351232 :
    ThetaLowerSegment 3124351232 3124482304 (156213847813033 / 50000)
      (156220354087081 / 50000) := by
  exact
    packedTile65536 3124351232 3124482304 14 5952 55895 32 _ _ (273281 / 12500) (2186251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3124482304 :
    ThetaLowerSegment 3124482304 3124613376 (156220354087081 / 50000)
      (156226908470577 / 50000) := by
  exact
    packedTile65536 3124482304 3124613376 14 5996 55897 32 _ _ (546563 / 25000) (437251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3124613376 :
    ThetaLowerSegment 3124613376 3124744448 (156226908470577 / 50000)
      (156233481449241 / 50000) := by
  exact
    packedTile65536 3124613376 3124744448 14 6013 55898 32 _ _ (136641 / 6250) (2186259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3124744448 :
    ThetaLowerSegment 3124744448 3124875520 (156233481449241 / 50000)
      (156240125493381 / 50000) := by
  exact
    packedTile65536 3124744448 3124875520 14 6078 55899 32 _ _ (109313 / 5000) (2186263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3124875520 :
    ThetaLowerSegment 3124875520 3125006592 (156240125493381 / 50000)
      (312493292057487 / 100000) := by
  exact
    packedTile65536 3124875520 3125006592 14 5965 55900 32 _ _ (437253 / 20000) (546567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125006592 :
    ThetaLowerSegment 3125006592 3125137664 (312493292057487 / 100000)
      (312506357201031 / 100000) := by
  exact
    packedTile65536 3125006592 3125137664 14 5976 55901 32 _ _ (2186269 / 100000) (68321 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125137664 :
    ThetaLowerSegment 3125137664 3125268736 (312506357201031 / 100000)
      (156259705718557 / 50000) := by
  exact
    packedTile65536 3125137664 3125268736 14 5971 55902 32 _ _ (2186273 / 100000) (546569 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125268736 :
    ThetaLowerSegment 3125268736 3125399808 (156259705718557 / 50000)
      (312532570638377 / 100000) := by
  exact
    packedTile65536 3125268736 3125399808 14 6019 55904 32 _ _ (2186277 / 100000) (54657 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125399808 :
    ThetaLowerSegment 3125399808 3125530880 (312532570638377 / 100000)
      (78136393112871 / 25000) := by
  exact
    packedTile65536 3125399808 3125530880 14 5947 55905 32 _ _ (2186281 / 100000) (546571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125530880 :
    ThetaLowerSegment 3125530880 3125661952 (78136393112871 / 25000) (156279347267027 / 50000) := by
  exact
    packedTile65536 3125530880 3125661952 14 6002 55906 32 _ _ (437257 / 20000) (136643 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125661952 :
    ThetaLowerSegment 3125661952 3125793024 (156279347267027 / 50000) (78142978757421 / 25000) := by
  exact
    packedTile65536 3125661952 3125793024 14 6047 55907 32 _ _ (218629 / 10000) (2186293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125793024 :
    ThetaLowerSegment 3125793024 3125924096 (78142978757421 / 25000) (39073135111519 / 12500) := by
  exact
    packedTile65536 3125793024 3125924096 14 6022 55908 32 _ _ (1093147 / 50000) (2186297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3125924096 :
    ThetaLowerSegment 3125924096 3126055168 (39073135111519 / 12500) (156299102619523 / 50000) := by
  exact
    packedTile65536 3125924096 3126055168 14 6003 55909 32 _ _ (1093149 / 50000) (2186301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126055168 :
    ThetaLowerSegment 3126055168 3126186240 (156299102619523 / 50000) (31261126183459 / 10000) := by
  exact
    packedTile65536 3126055168 3126186240 14 5972 55911 32 _ _ (1093151 / 50000) (437261 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126186240 :
    ThetaLowerSegment 3126186240 3126317312 (31261126183459 / 10000) (156312176717459 / 50000) := by
  exact
    packedTile65536 3126186240 3126317312 14 5988 55912 32 _ _ (1093153 / 50000) (2186309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126317312 :
    ThetaLowerSegment 3126317312 3126448384 (156312176717459 / 50000)
      (312637390407411 / 100000) := by
  exact
    packedTile65536 3126317312 3126448384 14 5963 55913 32 _ _ (2186311 / 100000) (1093157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126448384 :
    ThetaLowerSegment 3126448384 3126579456 (312637390407411 / 100000)
      (78162641831979 / 25000) := by
  exact
    packedTile65536 3126448384 3126579456 14 6027 55914 32 _ _ (437263 / 20000) (1093159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126579456 :
    ThetaLowerSegment 3126579456 3126710528 (78162641831979 / 25000)
      (312663486286887 / 100000) := by
  exact
    packedTile65536 3126579456 3126710528 14 5909 55915 32 _ _ (2186319 / 100000) (1093161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126710528 :
    ThetaLowerSegment 3126710528 3126841600 (312663486286887 / 100000)
      (312676556125781 / 100000) := by
  exact
    packedTile65536 3126710528 3126841600 14 5978 55916 32 _ _ (2186323 / 100000) (1093163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126841600 :
    ThetaLowerSegment 3126841600 3126972672 (312676556125781 / 100000)
      (156344919031153 / 50000) := by
  exact
    packedTile65536 3126841600 3126972672 14 6075 55918 32 _ _ (2186327 / 100000) (218633 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3126972672 :
    ThetaLowerSegment 3126972672 3127103744 (156344919031153 / 50000)
      (156351497704141 / 50000) := by
  exact
    packedTile65536 3126972672 3127103744 14 6018 55919 32 _ _ (546583 / 25000) (437267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3127103744 :
    ThetaLowerSegment 3127103744 3127234816 (156351497704141 / 50000)
      (156358031569277 / 50000) := by
  exact
    packedTile65536 3127103744 3127234816 14 5977 55920 32 _ _ (68323 / 3125) (2186339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3127234816 :
    ThetaLowerSegment 3127234816 3127365888 (156358031569277 / 50000)
      (156364590589277 / 50000) := by
  exact
    packedTile65536 3127234816 3127365888 14 6000 55921 32 _ _ (109317 / 5000) (2186343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3127365888 :
    ThetaLowerSegment 3127365888 3127496960 (156364590589277 / 50000)
      (156371138689557 / 50000) := by
  exact
    packedTile65536 3127365888 3127496960 14 5990 55922 32 _ _ (273293 / 12500) (2186347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3127496960 :
    ThetaLowerSegment 3127496960 3127628032 (156371138689557 / 50000)
      (156377671497381 / 50000) := by
  exact
    packedTile65536 3127496960 3127628032 14 5976 55924 32 _ _ (546587 / 25000) (2186351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3127628032 :
    ThetaLowerSegment 3127628032 3127759104 (156377671497381 / 50000)
      (156384178083909 / 50000) := by
  exact
    packedTile65536 3127628032 3127759104 14 5952 55925 32 _ _ (2186353 / 100000) (546589 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3127759104 :
    ThetaLowerSegment 3127759104 3127890176 (156384178083909 / 50000)
      (312781537714171 / 100000) := by
  exact
    packedTile65536 3127759104 3127890176 14 6029 55926 32 _ _ (2186357 / 100000) (54659 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3127890176 :
    ThetaLowerSegment 3127890176 3128021248 (312781537714171 / 100000)
      (39099337724219 / 12500) := by
  exact
    packedTile65536 3127890176 3128021248 14 6021 55927 32 _ _ (2186361 / 100000) (546591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128021248 :
    ThetaLowerSegment 3128021248 3128152320 (39099337724219 / 12500) (78201891591353 / 25000) := by
  exact
    packedTile65536 3128021248 3128152320 14 5884 55928 32 _ _ (437273 / 20000) (68324 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128152320 :
    ThetaLowerSegment 3128152320 3128283392 (78201891591353 / 25000)
      (312820542465427 / 100000) := by
  exact
    packedTile65536 3128152320 3128283392 14 5935 55929 32 _ _ (2186369 / 100000) (546593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128283392 :
    ThetaLowerSegment 3128283392 3128414464 (312820542465427 / 100000)
      (312833641032061 / 100000) := by
  exact
    packedTile65536 3128283392 3128414464 14 5991 55931 32 _ _ (1093187 / 50000) (2186377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128414464 :
    ThetaLowerSegment 3128414464 3128545536 (312833641032061 / 100000)
      (62569370662863 / 20000) := by
  exact
    packedTile65536 3128414464 3128545536 14 6043 55932 32 _ _ (1093189 / 50000) (2186381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128545536 :
    ThetaLowerSegment 3128545536 3128676608 (62569370662863 / 20000)
      (312859746408969 / 100000) := by
  exact
    packedTile65536 3128545536 3128676608 14 5897 55933 32 _ _ (1093191 / 50000) (437277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128676608 :
    ThetaLowerSegment 3128676608 3128807680 (312859746408969 / 100000)
      (312873039635849 / 100000) := by
  exact
    packedTile65536 3128676608 3128807680 14 6080 55934 32 _ _ (1093193 / 50000) (2186389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128807680 :
    ThetaLowerSegment 3128807680 3128938752 (312873039635849 / 100000)
      (312886206076429 / 100000) := by
  exact
    packedTile65536 3128807680 3128938752 14 6022 55935 32 _ _ (218639 / 10000) (2186393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3128938752 :
    ThetaLowerSegment 3128938752 3129069824 (312886206076429 / 100000)
      (312899317881247 / 100000) := by
  exact
    packedTile65536 3128938752 3129069824 14 5997 55936 32 _ _ (1093197 / 50000) (2186397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129069824 :
    ThetaLowerSegment 3129069824 3129200896 (312899317881247 / 100000)
      (62582514366397 / 20000) := by
  exact
    packedTile65536 3129069824 3129200896 14 6062 55938 32 _ _ (2186399 / 100000) (1093201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129200896 :
    ThetaLowerSegment 3129200896 3129331968 (62582514366397 / 20000) (9778924882333 / 3125) := by
  exact
    packedTile65536 3129200896 3129331968 14 5957 55939 32 _ _ (2186403 / 100000) (1093203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129331968 :
    ThetaLowerSegment 3129331968 3129463040 (9778924882333 / 3125) (62587754741929 / 20000) := by
  exact
    packedTile65536 3129331968 3129463040 14 6027 55940 32 _ _ (2186407 / 100000) (218641 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129463040 :
    ThetaLowerSegment 3129463040 3129594112 (62587754741929 / 20000)
      (312951879057179 / 100000) := by
  exact
    packedTile65536 3129463040 3129594112 14 5994 55941 32 _ _ (2186411 / 100000) (1093207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129594112 :
    ThetaLowerSegment 3129594112 3129725184 (312951879057179 / 100000)
      (312965106867929 / 100000) := by
  exact
    packedTile65536 3129594112 3129725184 14 6050 55942 32 _ _ (437283 / 20000) (1093209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129725184 :
    ThetaLowerSegment 3129725184 3129856256 (312965106867929 / 100000)
      (312978262557069 / 100000) := by
  exact
    packedTile65536 3129725184 3129856256 14 6017 55943 32 _ _ (109321 / 5000) (2186423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129856256 :
    ThetaLowerSegment 3129856256 3129987328 (312978262557069 / 100000)
      (312991464185181 / 100000) := by
  exact
    packedTile65536 3129856256 3129987328 14 6038 55945 32 _ _ (273303 / 12500) (2186427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3129987328 :
    ThetaLowerSegment 3129987328 3130118400 (312991464185181 / 100000)
      (313004407838941 / 100000) := by
  exact
    packedTile65536 3129987328 3130118400 14 5920 55946 32 _ _ (546607 / 25000) (2186431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130118400 :
    ThetaLowerSegment 3130118400 3130249472 (313004407838941 / 100000)
      (62603506160761 / 20000) := by
  exact
    packedTile65536 3130118400 3130249472 14 6002 55947 32 _ _ (68326 / 3125) (437287 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130249472 :
    ThetaLowerSegment 3130249472 3130380544 (62603506160761 / 20000)
      (313030745622989 / 100000) := by
  exact
    packedTile65536 3130249472 3130380544 14 6044 55948 32 _ _ (546609 / 25000) (2186439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130380544 :
    ThetaLowerSegment 3130380544 3130511616 (313030745622989 / 100000)
      (313043776811349 / 100000) := by
  exact
    packedTile65536 3130380544 3130511616 14 5960 55949 32 _ _ (2186441 / 100000) (546611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130511616 :
    ThetaLowerSegment 3130511616 3130642688 (313043776811349 / 100000)
      (313056877989789 / 100000) := by
  exact
    packedTile65536 3130511616 3130642688 14 5992 55950 32 _ _ (437289 / 20000) (136653 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130642688 :
    ThetaLowerSegment 3130642688 3130773760 (313056877989789 / 100000)
      (39133770083433 / 12500) := by
  exact
    packedTile65536 3130642688 3130773760 14 6075 55952 32 _ _ (2186449 / 100000) (546613 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130773760 :
    ThetaLowerSegment 3130773760 3130904832 (39133770083433 / 12500)
      (313083259707387 / 100000) := by
  exact
    packedTile65536 3130773760 3130904832 14 5991 55953 32 _ _ (2186453 / 100000) (273307 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3130904832 :
    ThetaLowerSegment 3130904832 3131035904 (313083259707387 / 100000)
      (39137061791451 / 12500) := by
  exact
    packedTile65536 3130904832 3131035904 14 6053 55954 32 _ _ (2186457 / 100000) (109323 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131035904 :
    ThetaLowerSegment 3131035904 3131166976 (39137061791451 / 12500) (1956934972537 / 625) := by
  exact
    packedTile65536 3131035904 3131166976 14 5992 55955 32 _ _ (2186461 / 100000) (68327 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131166976 :
    ThetaLowerSegment 3131166976 3131298048 (1956934972537 / 625) (31312268160493 / 10000) := by
  exact
    packedTile65536 3131166976 3131298048 14 5985 55956 32 _ _ (1093233 / 50000) (2186469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131298048 :
    ThetaLowerSegment 3131298048 3131429120 (31312268160493 / 10000) (7828394190697 / 2500) := by
  exact
    packedTile65536 3131298048 3131429120 14 5985 55958 32 _ _ (218647 / 10000) (2186473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131429120 :
    ThetaLowerSegment 3131429120 3131560192 (7828394190697 / 2500) (19571799391689 / 6250) := by
  exact
    packedTile65536 3131429120 3131560192 14 5956 55959 32 _ _ (1093237 / 50000) (2186477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131560192 :
    ThetaLowerSegment 3131560192 3131691264 (19571799391689 / 6250) (78290452139259 / 25000) := by
  exact
    packedTile65536 3131560192 3131691264 14 5954 55960 32 _ _ (1093239 / 50000) (2186481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131691264 :
    ThetaLowerSegment 3131691264 3131822336 (78290452139259 / 25000) (39146852265617 / 12500) := by
  exact
    packedTile65536 3131691264 3131822336 14 5950 55961 32 _ _ (1093241 / 50000) (437297 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131822336 :
    ThetaLowerSegment 3131822336 3131953408 (39146852265617 / 12500) (156593909488319 / 50000) := by
  exact
    packedTile65536 3131822336 3131953408 14 5946 55962 32 _ _ (2186487 / 100000) (218649 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3131953408 :
    ThetaLowerSegment 3131953408 3132084480 (156593909488319 / 50000)
      (156600398993607 / 50000) := by
  exact
    packedTile65536 3131953408 3132084480 14 5936 55963 32 _ _ (2186491 / 100000) (1093247 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3132084480 :
    ThetaLowerSegment 3132084480 3132215552 (156600398993607 / 50000)
      (313213717986169 / 100000) := by
  exact
    packedTile65536 3132084480 3132215552 14 5909 55965 32 _ _ (437299 / 20000) (1093249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3132215552 :
    ThetaLowerSegment 3132215552 3132346624 (313213717986169 / 100000)
      (156613399904843 / 50000) := by
  exact
    packedTile65536 3132215552 3132346624 14 5983 55966 32 _ _ (2186499 / 100000) (1093251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3132346624 :
    ThetaLowerSegment 3132346624 3132477696 (156613399904843 / 50000)
      (313239916641183 / 100000) := by
  exact
    packedTile65536 3132346624 3132477696 14 5999 55967 32 _ _ (2186503 / 100000) (1093253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3132477696 :
    ThetaLowerSegment 3132477696 3132608768 (313239916641183 / 100000)
      (313253092538391 / 100000) := by
  exact
    packedTile65536 3132477696 3132608768 14 6026 55968 32 _ _ (546627 / 25000) (2186511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3132608768 :
    ThetaLowerSegment 3132608768 3132739840 (313253092538391 / 100000)
      (313266049808503 / 100000) := by
  exact
    packedTile65536 3132608768 3132739840 14 5926 55969 32 _ _ (136657 / 6250) (437303 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3132739840 :
    ThetaLowerSegment 3132739840 3132870912 (313266049808503 / 100000)
      (313279061765219 / 100000) := by
  exact
    packedTile65536 3132739840 3132870912 14 5951 55970 32 _ _ (546629 / 25000) (2186519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3132870912 :
    ThetaLowerSegment 3132870912 3133001984 (313279061765219 / 100000)
      (313292312076419 / 100000) := by
  exact
    packedTile65536 3132870912 3133001984 14 6060 55972 32 _ _ (54663 / 2500) (2186523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133001984 :
    ThetaLowerSegment 3133001984 3133133056 (313292312076419 / 100000)
      (313305453085659 / 100000) := by
  exact
    packedTile65536 3133001984 3133133056 14 6010 55973 32 _ _ (546631 / 25000) (2186527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133133056 :
    ThetaLowerSegment 3133133056 3133264128 (313305453085659 / 100000)
      (313318585372827 / 100000) := by
  exact
    packedTile65536 3133133056 3133264128 14 6006 55974 32 _ _ (68329 / 3125) (2186531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133264128 :
    ThetaLowerSegment 3133264128 3133395200 (313318585372827 / 100000)
      (78332968233467 / 25000) := by
  exact
    packedTile65536 3133264128 3133395200 14 6077 55975 32 _ _ (2186533 / 100000) (273317 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133395200 :
    ThetaLowerSegment 3133395200 3133526272 (78332968233467 / 25000) (125337940887 / 40) := by
  exact
    packedTile65536 3133395200 3133526272 14 5936 55976 32 _ _ (2186537 / 100000) (109327 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133526272 :
    ThetaLowerSegment 3133526272 3133657344 (125337940887 / 40) (78339479746629 / 25000) := by
  exact
    packedTile65536 3133526272 3133657344 14 5976 55977 32 _ _ (2186541 / 100000) (136659 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133657344 :
    ThetaLowerSegment 3133657344 3133788416 (78339479746629 / 25000)
      (313370979219801 / 100000) := by
  exact
    packedTile65536 3133657344 3133788416 14 5973 55979 32 _ _ (437309 / 20000) (546637 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133788416 :
    ThetaLowerSegment 3133788416 3133919488 (313370979219801 / 100000)
      (78346015335617 / 25000) := by
  exact
    packedTile65536 3133788416 3133919488 14 5983 55980 32 _ _ (2186549 / 100000) (273319 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3133919488 :
    ThetaLowerSegment 3133919488 3134050560 (78346015335617 / 25000) (156698672329009 / 50000) := by
  exact
    packedTile65536 3133919488 3134050560 14 6075 55981 32 _ _ (1093277 / 50000) (2186557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134050560 :
    ThetaLowerSegment 3134050560 3134181632 (156698672329009 / 50000) (9794075975239 / 3125) := by
  exact
    packedTile65536 3134050560 3134181632 14 5985 55982 32 _ _ (1093279 / 50000) (2186561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134181632 :
    ThetaLowerSegment 3134181632 3134312704 (9794075975239 / 3125) (156711772009981 / 50000) := by
  exact
    packedTile65536 3134181632 3134312704 14 5997 55983 32 _ _ (1093281 / 50000) (437313 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134312704 :
    ThetaLowerSegment 3134312704 3134443776 (156711772009981 / 50000) (1958980690612 / 625) := by
  exact
    packedTile65536 3134312704 3134443776 14 6113 55984 32 _ _ (1093283 / 50000) (2186569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134443776 :
    ThetaLowerSegment 3134443776 3134574848 (1958980690612 / 625) (3918122531433 / 1250) := by
  exact
    packedTile65536 3134443776 3134574848 14 5896 55986 32 _ _ (218657 / 10000) (2186573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134574848 :
    ThetaLowerSegment 3134574848 3134705920 (3918122531433 / 1250) (78365685664893 / 25000) := by
  exact
    packedTile65536 3134574848 3134705920 14 5918 55987 32 _ _ (1093287 / 50000) (2186577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134705920 :
    ThetaLowerSegment 3134705920 3134836992 (78365685664893 / 25000) (156737920133891 / 50000) := by
  exact
    packedTile65536 3134705920 3134836992 14 5990 55988 32 _ _ (2186579 / 100000) (1093291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134836992 :
    ThetaLowerSegment 3134836992 3134968064 (156737920133891 / 50000)
      (156744458017061 / 50000) := by
  exact
    packedTile65536 3134836992 3134968064 14 5980 55989 32 _ _ (2186583 / 100000) (1093293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3134968064 :
    ThetaLowerSegment 3134968064 3135099136 (156744458017061 / 50000) (62700380434863 / 20000) := by
  exact
    packedTile65536 3134968064 3135099136 14 5939 55990 32 _ _ (2186587 / 100000) (218659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3135099136 :
    ThetaLowerSegment 3135099136 3135230208 (62700380434863 / 20000) (156757490087543 / 50000) := by
  exact
    packedTile65536 3135099136 3135230208 14 5981 55991 32 _ _ (2186591 / 100000) (1093297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3135230208 :
    ThetaLowerSegment 3135230208 3135361280 (156757490087543 / 50000)
      (313528185022291 / 100000) := by
  exact
    packedTile65536 3135230208 3135361280 14 6039 55993 32 _ _ (437319 / 20000) (1093299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3135361280 :
    ThetaLowerSegment 3135361280 3135492352 (313528185022291 / 100000)
      (313541169053091 / 100000) := by
  exact
    packedTile65536 3135361280 3135492352 14 5938 55994 32 _ _ (10933 / 500) (2186603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3135492352 :
    ThetaLowerSegment 3135492352 3135623424 (313541169053091 / 100000)
      (313554369581439 / 100000) := by
  exact
    packedTile65536 3135492352 3135623424 14 6037 55995 32 _ _ (546651 / 25000) (2186607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3135623424 :
    ThetaLowerSegment 3135623424 3135754496 (313554369581439 / 100000)
      (62713487787491 / 20000) := by
  exact
    packedTile65536 3135623424 3135754496 14 5977 55996 32 _ _ (136663 / 6250) (2186611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3135754496 :
    ThetaLowerSegment 3135754496 3135885568 (62713487787491 / 20000)
      (313580597968471 / 100000) := by
  exact
    packedTile65536 3135754496 3135885568 14 6018 55997 32 _ _ (546653 / 25000) (437323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3135885568 :
    ThetaLowerSegment 3135885568 3136016640 (313580597968471 / 100000)
      (313593558041503 / 100000) := by
  exact
    packedTile65536 3135885568 3136016640 14 5927 55998 32 _ _ (273327 / 12500) (2186619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136016640 :
    ThetaLowerSegment 3136016640 3136147712 (313593558041503 / 100000)
      (313606671201643 / 100000) := by
  exact
    packedTile65536 3136016640 3136147712 14 5997 56000 32 _ _ (109331 / 5000) (2186623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136147712 :
    ThetaLowerSegment 3136147712 3136278784 (313606671201643 / 100000)
      (156809894382509 / 50000) := by
  exact
    packedTile65536 3136147712 3136278784 14 5999 56001 32 _ _ (17493 / 800) (546657 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136278784 :
    ThetaLowerSegment 3136278784 3136409856 (156809894382509 / 50000)
      (156816467389283 / 50000) := by
  exact
    packedTile65536 3136278784 3136409856 14 6012 56002 32 _ _ (2186629 / 100000) (273329 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136409856 :
    ThetaLowerSegment 3136409856 3136540928 (156816467389283 / 50000) (62729207854027 / 20000) := by
  exact
    packedTile65536 3136409856 3136540928 14 5993 56003 32 _ _ (2186633 / 100000) (546659 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136540928 :
    ThetaLowerSegment 3136540928 3136672000 (62729207854027 / 20000) (78414785946419 / 25000) := by
  exact
    packedTile65536 3136540928 3136672000 14 5993 56004 32 _ _ (2186637 / 100000) (27333 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136672000 :
    ThetaLowerSegment 3136672000 3136803072 (78414785946419 / 25000) (78418048414791 / 25000) := by
  exact
    packedTile65536 3136672000 3136803072 14 5968 56005 32 _ _ (2186641 / 100000) (546661 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136803072 :
    ThetaLowerSegment 3136803072 3136934144 (78418048414791 / 25000)
      (313685438167929 / 100000) := by
  exact
    packedTile65536 3136803072 3136934144 14 6057 56007 32 _ _ (437329 / 20000) (273331 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3136934144 :
    ThetaLowerSegment 3136934144 3137065216 (313685438167929 / 100000)
      (313698481535179 / 100000) := by
  exact
    packedTile65536 3136934144 3137065216 14 5965 56008 32 _ _ (43733 / 2000) (2186653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137065216 :
    ThetaLowerSegment 3137065216 3137196288 (313698481535179 / 100000)
      (313711579592639 / 100000) := by
  exact
    packedTile65536 3137065216 3137196288 14 5990 56009 32 _ _ (1093327 / 50000) (2186657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137196288 :
    ThetaLowerSegment 3137196288 3137327360 (313711579592639 / 100000)
      (62744951716081 / 20000) := by
  exact
    packedTile65536 3137196288 3137327360 14 6027 56010 32 _ _ (1093329 / 50000) (2186661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137327360 :
    ThetaLowerSegment 3137327360 3137458432 (62744951716081 / 20000) (12549511643437 / 4000) := by
  exact
    packedTile65536 3137327360 3137458432 14 5960 56011 32 _ _ (1093331 / 50000) (437333 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137458432 :
    ThetaLowerSegment 3137458432 3137589504 (12549511643437 / 4000) (313750919828589 / 100000) := by
  exact
    packedTile65536 3137458432 3137589504 14 6004 56013 32 _ _ (1093333 / 50000) (2186669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137589504 :
    ThetaLowerSegment 3137589504 3137720576 (313750919828589 / 100000) (9805131507133 / 3125) := by
  exact
    packedTile65536 3137589504 3137720576 14 6077 56014 32 _ _ (2186671 / 100000) (1093337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137720576 :
    ThetaLowerSegment 3137720576 3137851648 (9805131507133 / 3125) (78444316762839 / 25000) := by
  exact
    packedTile65536 3137720576 3137851648 14 5972 56015 32 _ _ (87467 / 4000) (1093339 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137851648 :
    ThetaLowerSegment 3137851648 3137982720 (78444316762839 / 25000)
      (313790424298899 / 100000) := by
  exact
    packedTile65536 3137851648 3137982720 14 6017 56016 32 _ _ (2186679 / 100000) (1093341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3137982720 :
    ThetaLowerSegment 3137982720 3138113792 (313790424298899 / 100000)
      (313803566263729 / 100000) := by
  exact
    packedTile65536 3137982720 3138113792 14 6010 56017 32 _ _ (2186683 / 100000) (1093343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138113792 :
    ThetaLowerSegment 3138113792 3138244864 (313803566263729 / 100000)
      (62763353895967 / 20000) := by
  exact
    packedTile65536 3138113792 3138244864 14 6038 56018 32 _ _ (2186687 / 100000) (218669 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138244864 :
    ThetaLowerSegment 3138244864 3138375936 (62763353895967 / 20000)
      (313829837145251 / 100000) := by
  exact
    packedTile65536 3138244864 3138375936 14 5976 56020 32 _ _ (2186691 / 100000) (1093347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138375936 :
    ThetaLowerSegment 3138375936 3138507008 (313829837145251 / 100000)
      (62768560413167 / 20000) := by
  exact
    packedTile65536 3138375936 3138507008 14 5929 56021 32 _ _ (273337 / 12500) (2186699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138507008 :
    ThetaLowerSegment 3138507008 3138638080 (62768560413167 / 20000) (62771188389227 / 20000) := by
  exact
    packedTile65536 3138507008 3138638080 14 6009 56022 32 _ _ (21867 / 1000) (2186703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138638080 :
    ThetaLowerSegment 3138638080 3138769152 (62771188389227 / 20000) (62773775260059 / 20000) := by
  exact
    packedTile65536 3138638080 3138769152 14 5915 56023 32 _ _ (136669 / 6250) (2186707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138769152 :
    ThetaLowerSegment 3138769152 3138900224 (62773775260059 / 20000)
      (313881885026187 / 100000) := by
  exact
    packedTile65536 3138769152 3138900224 14 5949 56024 32 _ _ (546677 / 25000) (2186711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3138900224 :
    ThetaLowerSegment 3138900224 3139031296 (313881885026187 / 100000)
      (313895029352019 / 100000) := by
  exact
    packedTile65536 3138900224 3139031296 14 6011 56025 32 _ _ (273339 / 12500) (437343 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139031296 :
    ThetaLowerSegment 3139031296 3139162368 (313895029352019 / 100000)
      (39238508046507 / 12500) := by
  exact
    packedTile65536 3139031296 3139162368 14 5961 56027 32 _ _ (2186717 / 100000) (13667 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139162368 :
    ThetaLowerSegment 3139162368 3139293440 (39238508046507 / 12500) (156960559548213 / 50000) := by
  exact
    packedTile65536 3139162368 3139293440 14 5970 56028 32 _ _ (2186721 / 100000) (546681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139293440 :
    ThetaLowerSegment 3139293440 3139424512 (156960559548213 / 50000)
      (156967132843563 / 50000) := by
  exact
    packedTile65536 3139293440 3139424512 14 6012 56029 32 _ _ (87469 / 4000) (273341 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139424512 :
    ThetaLowerSegment 3139424512 3139555584 (156967132843563 / 50000)
      (313947248297199 / 100000) := by
  exact
    packedTile65536 3139424512 3139555584 14 5937 56030 32 _ _ (2186729 / 100000) (546683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139555584 :
    ThetaLowerSegment 3139555584 3139686656 (313947248297199 / 100000)
      (313960473658383 / 100000) := by
  exact
    packedTile65536 3139555584 3139686656 14 6048 56031 32 _ _ (2186733 / 100000) (136671 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139686656 :
    ThetaLowerSegment 3139686656 3139817728 (313960473658383 / 100000)
      (31397353066501 / 10000) := by
  exact
    packedTile65536 3139686656 3139817728 14 5971 56032 32 _ _ (2186737 / 100000) (109337 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139817728 :
    ThetaLowerSegment 3139817728 3139948800 (31397353066501 / 10000) (78496651298857 / 25000) := by
  exact
    packedTile65536 3139817728 3139948800 14 5979 56034 32 _ _ (1093371 / 50000) (437349 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3139948800 :
    ThetaLowerSegment 3139948800 3140079872 (78496651298857 / 25000) (78499929231111 / 25000) := by
  exact
    packedTile65536 3139948800 3140079872 14 5996 56035 32 _ _ (1093373 / 50000) (2186749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140079872 :
    ThetaLowerSegment 3140079872 3140210944 (78499929231111 / 25000) (39251620531993 / 12500) := by
  exact
    packedTile65536 3140079872 3140210944 14 6058 56036 32 _ _ (8747 / 400) (2186753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140210944 :
    ThetaLowerSegment 3140210944 3140342016 (39251620531993 / 12500) (157012956013189 / 50000) := by
  exact
    packedTile65536 3140210944 3140342016 14 5921 56037 32 _ _ (1093377 / 50000) (2186757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140342016 :
    ThetaLowerSegment 3140342016 3140473088 (157012956013189 / 50000) (78509755410147 / 25000) := by
  exact
    packedTile65536 3140342016 3140473088 14 5995 56038 32 _ _ (1093379 / 50000) (2186761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140473088 :
    ThetaLowerSegment 3140473088 3140604160 (78509755410147 / 25000) (78513050860481 / 25000) := by
  exact
    packedTile65536 3140473088 3140604160 14 6028 56039 32 _ _ (1093381 / 50000) (437353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140604160 :
    ThetaLowerSegment 3140604160 3140735232 (78513050860481 / 25000)
      (314065426821973 / 100000) := by
  exact
    packedTile65536 3140604160 3140735232 14 6047 56041 32 _ _ (2186767 / 100000) (218677 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140735232 :
    ThetaLowerSegment 3140735232 3140866304 (314065426821973 / 100000)
      (157039342607273 / 50000) := by
  exact
    packedTile65536 3140735232 3140866304 14 6063 56042 32 _ _ (2186771 / 100000) (1093387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140866304 :
    ThetaLowerSegment 3140866304 3140997376 (157039342607273 / 50000)
      (314091742448071 / 100000) := by
  exact
    packedTile65536 3140866304 3140997376 14 5971 56043 32 _ _ (87471 / 4000) (1093389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3140997376 :
    ThetaLowerSegment 3140997376 3141128448 (314091742448071 / 100000)
      (157052380171729 / 50000) := by
  exact
    packedTile65536 3140997376 3141128448 14 5953 56044 32 _ _ (2186779 / 100000) (1093391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3141128448 :
    ThetaLowerSegment 3141128448 3141259520 (157052380171729 / 50000)
      (314117861360411 / 100000) := by
  exact
    packedTile65536 3141128448 3141259520 14 5991 56045 32 _ _ (2186783 / 100000) (1093393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3141259520 :
    ThetaLowerSegment 3141259520 3141390592 (314117861360411 / 100000)
      (62826179796901 / 20000) := by
  exact
    packedTile65536 3141259520 3141390592 14 5962 56046 32 _ _ (2186787 / 100000) (218679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3141390592 :
    ThetaLowerSegment 3141390592 3141521664 (62826179796901 / 20000)
      (314144203427033 / 100000) := by
  exact
    packedTile65536 3141390592 3141521664 14 6084 56048 32 _ _ (273349 / 12500) (437359 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3141521664 :
    ThetaLowerSegment 3141521664 3141652736 (314144203427033 / 100000)
      (314157472905161 / 100000) := by
  exact
    packedTile65536 3141521664 3141652736 14 6068 56049 32 _ _ (546699 / 25000) (2186799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3141652736 :
    ThetaLowerSegment 3141652736 3141783808 (314157472905161 / 100000)
      (314170644001561 / 100000) := by
  exact
    packedTile65536 3141652736 3141783808 14 6023 56050 32 _ _ (5467 / 250) (2186803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3141783808 :
    ThetaLowerSegment 3141783808 3141914880 (314170644001561 / 100000)
      (314183721089481 / 100000) := by
  exact
    packedTile65536 3141783808 3141914880 14 5980 56051 32 _ _ (546701 / 25000) (2186807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3141914880 :
    ThetaLowerSegment 3141914880 3142045952 (314183721089481 / 100000)
      (314196900981297 / 100000) := by
  exact
    packedTile65536 3141914880 3142045952 14 6027 56052 32 _ _ (273351 / 12500) (2186811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142045952 :
    ThetaLowerSegment 3142045952 3142177024 (314196900981297 / 100000)
      (62841954512523 / 20000) := by
  exact
    packedTile65536 3142045952 3142177024 14 5886 56053 32 _ _ (2186813 / 100000) (68338 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142177024 :
    ThetaLowerSegment 3142177024 3142308096 (62841954512523 / 20000)
      (314222976563661 / 100000) := by
  exact
    packedTile65536 3142177024 3142308096 14 6038 56055 32 _ _ (2186817 / 100000) (109341 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142308096 :
    ThetaLowerSegment 3142308096 3142439168 (314222976563661 / 100000)
      (157117966739043 / 50000) := by
  exact
    packedTile65536 3142308096 3142439168 14 5925 56056 32 _ _ (2186821 / 100000) (273353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142439168 :
    ThetaLowerSegment 3142439168 3142570240 (157117966739043 / 50000)
      (314249025999361 / 100000) := by
  exact
    packedTile65536 3142439168 3142570240 14 5987 56057 32 _ _ (87473 / 4000) (546707 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142570240 :
    ThetaLowerSegment 3142570240 3142701312 (314249025999361 / 100000)
      (78565527449317 / 25000) := by
  exact
    packedTile65536 3142570240 3142701312 14 5983 56058 32 _ _ (2186829 / 100000) (136677 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142701312 :
    ThetaLowerSegment 3142701312 3142832384 (78565527449317 / 25000) (12571007394871 / 4000) := by
  exact
    packedTile65536 3142701312 3142832384 14 5979 56059 32 _ _ (2186833 / 100000) (546709 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142832384 :
    ThetaLowerSegment 3142832384 3142963456 (12571007394871 / 4000) (314288386812781 / 100000) := by
  exact
    packedTile65536 3142832384 3142963456 14 6037 56060 32 _ _ (1093419 / 50000) (2186841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3142963456 :
    ThetaLowerSegment 3142963456 3143094528 (314288386812781 / 100000)
      (314301569096357 / 100000) := by
  exact
    packedTile65536 3142963456 3143094528 14 6028 56062 32 _ _ (1093421 / 50000) (437369 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3143094528 :
    ThetaLowerSegment 3143094528 3143225600 (314301569096357 / 100000)
      (314314591764287 / 100000) := by
  exact
    packedTile65536 3143094528 3143225600 14 5955 56063 32 _ _ (1093423 / 50000) (2186849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3143225600 :
    ThetaLowerSegment 3143225600 3143356672 (314314591764287 / 100000)
      (314327695369487 / 100000) := by
  exact
    packedTile65536 3143225600 3143356672 14 5992 56064 32 _ _ (43737 / 2000) (2186853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3143356672 :
    ThetaLowerSegment 3143356672 3143487744 (314327695369487 / 100000)
      (314340516894489 / 100000) := by
  exact
    packedTile65536 3143356672 3143487744 14 5863 56065 32 _ _ (1093427 / 50000) (2186857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3143487744 :
    ThetaLowerSegment 3143487744 3143618816 (314340516894489 / 100000)
      (62870728483241 / 20000) := by
  exact
    packedTile65536 3143487744 3143618816 14 6002 56066 32 _ _ (1093429 / 50000) (2186861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3143618816 :
    ThetaLowerSegment 3143618816 3143749888 (62870728483241 / 20000) (31436688387167 / 10000) := by
  exact
    packedTile65536 3143618816 3143749888 14 6055 56067 32 _ _ (2186863 / 100000) (1093433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3143749888 :
    ThetaLowerSegment 3143749888 3143880960 (31436688387167 / 10000)
      (314379845432379 / 100000) := by
  exact
    packedTile65536 3143749888 3143880960 14 5927 56069 32 _ _ (2186867 / 100000) (218687 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3143880960 :
    ThetaLowerSegment 3143880960 3144012032 (314379845432379 / 100000)
      (78598232370393 / 25000) := by
  exact
    packedTile65536 3143880960 3144012032 14 5983 56070 32 _ _ (2186871 / 100000) (1093437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144012032 :
    ThetaLowerSegment 3144012032 3144143104 (78598232370393 / 25000)
      (314406280353447 / 100000) := by
  exact
    packedTile65536 3144012032 3144143104 14 6105 56071 32 _ _ (3499 / 160) (1093439 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144143104 :
    ThetaLowerSegment 3144143104 3144274176 (314406280353447 / 100000) (12576778864303 / 4000) := by
  exact
    packedTile65536 3144143104 3144274176 14 6032 56072 32 _ _ (2186879 / 100000) (1093441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144274176 :
    ThetaLowerSegment 3144274176 3144405248 (12576778864303 / 4000) (62886536076179 / 20000) := by
  exact
    packedTile65536 3144274176 3144405248 14 6040 56073 32 _ _ (2186883 / 100000) (1093443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144405248 :
    ThetaLowerSegment 3144405248 3144536320 (62886536076179 / 20000) (62889138472899 / 20000) := by
  exact
    packedTile65536 3144405248 3144536320 14 5950 56074 32 _ _ (273361 / 12500) (2186891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144536320 :
    ThetaLowerSegment 3144536320 3144667392 (62889138472899 / 20000) (62891756182623 / 20000) := by
  exact
    packedTile65536 3144536320 3144667392 14 5985 56076 32 _ _ (546723 / 25000) (437379 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144667392 :
    ThetaLowerSegment 3144667392 3144798464 (62891756182623 / 20000)
      (314471747019499 / 100000) := by
  exact
    packedTile65536 3144667392 3144798464 14 5929 56077 32 _ _ (136681 / 6250) (2186899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144798464 :
    ThetaLowerSegment 3144798464 3144929536 (314471747019499 / 100000)
      (314484724084099 / 100000) := by
  exact
    packedTile65536 3144798464 3144929536 14 5934 56078 32 _ _ (21869 / 1000) (2186903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3144929536 :
    ThetaLowerSegment 3144929536 3145060608 (314484724084099 / 100000)
      (314497867377139 / 100000) := by
  exact
    packedTile65536 3144929536 3145060608 14 6010 56079 32 _ _ (273363 / 12500) (2186907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145060608 :
    ThetaLowerSegment 3145060608 3145191680 (314497867377139 / 100000)
      (314510991012047 / 100000) := by
  exact
    packedTile65536 3145060608 3145191680 14 6001 56080 32 _ _ (546727 / 25000) (2186911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145191680 :
    ThetaLowerSegment 3145191680 3145322752 (314510991012047 / 100000)
      (157262081394523 / 50000) := by
  exact
    packedTile65536 3145191680 3145322752 14 6023 56082 32 _ _ (2186913 / 100000) (546729 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145322752 :
    ThetaLowerSegment 3145322752 3145339136 (157262081394523 / 50000)
      (314525822659049 / 100000) := by
  exact
    packedTile65536 3145322752 3145339136 11 759 56083 32 _ _ (2186917 / 100000) (54673 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145339136 :
    ThetaLowerSegment 3145339136 3145341184 (314525822659049 / 100000)
      (314525997612409 / 100000) := by
  exact
    packedTile65536 3145339136 3145341184 8 80 56083 32 _ _ (2186917 / 100000) (54673 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3113341184_3145341184 :
    ThetaLowerSegment 3113341184 3145341184 (77831487911313 / 25000)
      (314525997612409 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3113341184 cell3113472256)
                  (ThetaLowerSegment.join cell3113603328 cell3113734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3113865472 cell3113996544)
                  (ThetaLowerSegment.join cell3114127616 cell3114258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3114389760 cell3114520832)
                  (ThetaLowerSegment.join cell3114651904 cell3114782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3114914048 cell3115045120)
                  (ThetaLowerSegment.join cell3115176192 cell3115307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3115438336 cell3115569408)
                  (ThetaLowerSegment.join cell3115700480 cell3115831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3115962624 cell3116093696)
                  (ThetaLowerSegment.join cell3116224768 cell3116355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3116486912 cell3116617984)
                  (ThetaLowerSegment.join cell3116749056 cell3116880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3117011200 cell3117142272)
                  (ThetaLowerSegment.join cell3117273344 cell3117404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3117535488 cell3117666560)
                  (ThetaLowerSegment.join cell3117797632 cell3117928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3118059776 cell3118190848)
                  (ThetaLowerSegment.join cell3118321920 cell3118452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3118584064 cell3118715136)
                  (ThetaLowerSegment.join cell3118846208 cell3118977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3119108352 cell3119239424)
                  (ThetaLowerSegment.join cell3119370496 cell3119501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3119632640 cell3119763712)
                  (ThetaLowerSegment.join cell3119894784 cell3120025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3120156928 cell3120288000)
                  (ThetaLowerSegment.join cell3120419072 cell3120550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3120681216 cell3120812288)
                  (ThetaLowerSegment.join cell3120943360 cell3121074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3121205504 cell3121336576)
                  (ThetaLowerSegment.join cell3121467648 cell3121598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3121729792 cell3121860864)
                  (ThetaLowerSegment.join cell3121991936 cell3122123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3122254080 cell3122385152)
                  (ThetaLowerSegment.join cell3122516224 cell3122647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3122778368 cell3122909440)
                  (ThetaLowerSegment.join cell3123040512 cell3123171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3123302656 cell3123433728)
                  (ThetaLowerSegment.join cell3123564800 cell3123695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3123826944 cell3123958016)
                  (ThetaLowerSegment.join cell3124089088 cell3124220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3124351232 cell3124482304)
                  (ThetaLowerSegment.join cell3124613376 cell3124744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3124875520 cell3125006592)
                  (ThetaLowerSegment.join cell3125137664 cell3125268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3125399808 cell3125530880)
                  (ThetaLowerSegment.join cell3125661952 cell3125793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3125924096 cell3126055168)
                  (ThetaLowerSegment.join cell3126186240 cell3126317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3126448384 cell3126579456)
                  (ThetaLowerSegment.join cell3126710528 cell3126841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3126972672 cell3127103744)
                  (ThetaLowerSegment.join cell3127234816 cell3127365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3127496960 cell3127628032)
                  (ThetaLowerSegment.join cell3127759104 cell3127890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3128021248 cell3128152320)
                  (ThetaLowerSegment.join cell3128283392 cell3128414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3128545536 cell3128676608)
                  (ThetaLowerSegment.join cell3128807680 cell3128938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3129069824 cell3129200896)
                  (ThetaLowerSegment.join cell3129331968 cell3129463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3129594112 cell3129725184)
                  (ThetaLowerSegment.join cell3129856256 cell3129987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3130118400 cell3130249472)
                  (ThetaLowerSegment.join cell3130380544 cell3130511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3130642688 cell3130773760)
                  (ThetaLowerSegment.join cell3130904832 cell3131035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3131166976 cell3131298048)
                  (ThetaLowerSegment.join cell3131429120 cell3131560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3131691264 cell3131822336)
                  (ThetaLowerSegment.join cell3131953408 cell3132084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3132215552 cell3132346624)
                  (ThetaLowerSegment.join cell3132477696 cell3132608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3132739840 cell3132870912)
                  (ThetaLowerSegment.join cell3133001984 cell3133133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3133264128 cell3133395200)
                  (ThetaLowerSegment.join cell3133526272 cell3133657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3133788416 cell3133919488)
                  (ThetaLowerSegment.join cell3134050560 cell3134181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3134312704 cell3134443776)
                  (ThetaLowerSegment.join cell3134574848 cell3134705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3134836992 cell3134968064)
                  (ThetaLowerSegment.join cell3135099136 cell3135230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3135361280 cell3135492352)
                  (ThetaLowerSegment.join cell3135623424 cell3135754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3135885568 cell3136016640)
                  (ThetaLowerSegment.join cell3136147712 cell3136278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3136409856 cell3136540928)
                  (ThetaLowerSegment.join cell3136672000 cell3136803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3136934144 cell3137065216)
                  (ThetaLowerSegment.join cell3137196288 cell3137327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3137458432 cell3137589504)
                  (ThetaLowerSegment.join cell3137720576 cell3137851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3137982720 cell3138113792)
                  (ThetaLowerSegment.join cell3138244864 cell3138375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3138507008 cell3138638080)
                  (ThetaLowerSegment.join cell3138769152 cell3138900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3139031296 cell3139162368)
                  (ThetaLowerSegment.join cell3139293440 cell3139424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3139555584 cell3139686656)
                  (ThetaLowerSegment.join cell3139817728 cell3139948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3140079872 cell3140210944)
                  (ThetaLowerSegment.join cell3140342016 cell3140473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3140604160 cell3140735232)
                  (ThetaLowerSegment.join cell3140866304 cell3140997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3141128448 cell3141259520)
                  (ThetaLowerSegment.join cell3141390592 cell3141521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3141652736 cell3141783808)
                  (ThetaLowerSegment.join cell3141914880 cell3142045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3142177024 cell3142308096)
                  (ThetaLowerSegment.join cell3142439168 cell3142570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3142701312 cell3142832384)
                  (ThetaLowerSegment.join cell3142963456 cell3143094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3143225600 cell3143356672)
                  (ThetaLowerSegment.join cell3143487744 cell3143618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3143749888 cell3143880960)
                  (ThetaLowerSegment.join cell3144012032 cell3144143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3144274176 cell3144405248)
                  (ThetaLowerSegment.join cell3144536320 cell3144667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3144798464 cell3144929536)
                (ThetaLowerSegment.join cell3145060608 cell3145191680))
              (ThetaLowerSegment.join cell3145322752 cell3145339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
