/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2953341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2921341184 :
    ThetaLowerSegment 2921341184 2921472256 (14606402076837 / 5000) (9129406417976 / 3125) := by
  exact
    packedTile65536 2921341184 2921472256 14 5948 54049 31 _ _ (2179529 / 100000) (544883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921472256 :
    ThetaLowerSegment 2921472256 2921603328 (9129406417976 / 3125) (146077129560743 / 50000) := by
  exact
    packedTile65536 2921472256 2921603328 14 6081 54050 31 _ _ (1089767 / 50000) (2179537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921603328 :
    ThetaLowerSegment 2921603328 2921734400 (146077129560743 / 50000)
      (146083735740421 / 50000) := by
  exact
    packedTile65536 2921603328 2921734400 14 6062 54051 31 _ _ (1089769 / 50000) (2179541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921734400 :
    ThetaLowerSegment 2921734400 2921865472 (146083735740421 / 50000) (9130640649653 / 3125) := by
  exact
    packedTile65536 2921734400 2921865472 14 5978 54053 31 _ _ (2179543 / 100000) (1089773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921865472 :
    ThetaLowerSegment 2921865472 2921996544 (9130640649653 / 3125) (146096782496807 / 50000) := by
  exact
    packedTile65536 2921865472 2921996544 14 5994 54054 31 _ _ (2179547 / 100000) (43591 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2921996544 :
    ThetaLowerSegment 2921996544 2922127616 (146096782496807 / 50000) (29220661615099 / 10000) := by
  exact
    packedTile65536 2921996544 2922127616 14 5988 54055 31 _ _ (68111 / 3125) (435911 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2922127616 :
    ThetaLowerSegment 2922127616 2922258688 (29220661615099 / 10000) (146109907771063 / 50000) := by
  exact
    packedTile65536 2922127616 2922258688 14 6056 54056 31 _ _ (544889 / 25000) (2179559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2922258688 :
    ThetaLowerSegment 2922258688 2922389760 (146109907771063 / 50000)
      (292232943038029 / 100000) := by
  exact
    packedTile65536 2922258688 2922389760 14 6023 54057 31 _ _ (2179561 / 100000) (544891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2922389760 :
    ThetaLowerSegment 2922389760 2922520832 (292232943038029 / 100000) (18265371781399 / 6250) := by
  exact
    packedTile65536 2922389760 2922520832 14 5967 54059 31 _ _ (435913 / 20000) (136223 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2922520832 :
    ThetaLowerSegment 2922520832 2922651904 (18265371781399 / 6250) (146129546744527 / 50000) := by
  exact
    packedTile65536 2922520832 2922651904 14 6031 54060 31 _ _ (217957 / 10000) (2179573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2922651904 :
    ThetaLowerSegment 2922651904 2922782976 (146129546744527 / 50000)
      (146136153033321 / 50000) := by
  exact
    packedTile65536 2922651904 2922782976 14 6062 54061 31 _ _ (1089787 / 50000) (2179577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2922782976 :
    ThetaLowerSegment 2922782976 2922914048 (146136153033321 / 50000)
      (146142739721059 / 50000) := by
  exact
    packedTile65536 2922782976 2922914048 14 6044 54062 31 _ _ (2179579 / 100000) (1089791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2922914048 :
    ThetaLowerSegment 2922914048 2923045120 (146142739721059 / 50000)
      (292298711690511 / 100000) := by
  exact
    packedTile65536 2922914048 2923045120 14 6071 54063 31 _ _ (2179583 / 100000) (1089793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923045120 :
    ThetaLowerSegment 2923045120 2923176192 (292298711690511 / 100000)
      (292311815373567 / 100000) := by
  exact
    packedTile65536 2923045120 2923176192 14 6012 54065 31 _ _ (544897 / 25000) (2179591 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923176192 :
    ThetaLowerSegment 2923176192 2923307264 (292311815373567 / 100000)
      (292324820999031 / 100000) := by
  exact
    packedTile65536 2923176192 2923307264 14 5967 54066 31 _ _ (272449 / 12500) (435919 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923307264 :
    ThetaLowerSegment 2923307264 2923438336 (292324820999031 / 100000)
      (146168987433463 / 50000) := by
  exact
    packedTile65536 2923307264 2923438336 14 6035 54067 31 _ _ (2179597 / 100000) (5449 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923438336 :
    ThetaLowerSegment 2923438336 2923569408 (146168987433463 / 50000)
      (146175513158857 / 50000) := by
  exact
    packedTile65536 2923438336 2923569408 14 5988 54068 31 _ _ (2179601 / 100000) (544901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923569408 :
    ThetaLowerSegment 2923569408 2923700480 (146175513158857 / 50000)
      (146182034540009 / 50000) := by
  exact
    packedTile65536 2923569408 2923700480 14 5984 54070 31 _ _ (1089803 / 50000) (2179609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923700480 :
    ThetaLowerSegment 2923700480 2923831552 (146182034540009 / 50000) (73094319924057 / 25000) := by
  exact
    packedTile65536 2923700480 2923831552 14 6061 54071 31 _ _ (217961 / 10000) (2179613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923831552 :
    ThetaLowerSegment 2923831552 2923962624 (73094319924057 / 25000) (36548793583471 / 12500) := by
  exact
    packedTile65536 2923831552 2923962624 14 5996 54072 31 _ _ (435923 / 20000) (1089809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2923962624 :
    ThetaLowerSegment 2923962624 2924093696 (36548793583471 / 12500)
      (292403297784247 / 100000) := by
  exact
    packedTile65536 2923962624 2924093696 14 5941 54073 31 _ _ (2179619 / 100000) (1089811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2924093696 :
    ThetaLowerSegment 2924093696 2924224768 (292403297784247 / 100000)
      (292416214236071 / 100000) := by
  exact
    packedTile65536 2924093696 2924224768 14 5926 54074 31 _ _ (272453 / 12500) (2179627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2924224768 :
    ThetaLowerSegment 2924224768 2924355840 (292416214236071 / 100000)
      (292429333417003 / 100000) := by
  exact
    packedTile65536 2924224768 2924355840 14 6019 54076 31 _ _ (544907 / 25000) (2179631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2924355840 :
    ThetaLowerSegment 2924355840 2924486912 (292429333417003 / 100000)
      (58488470908909 / 20000) := by
  exact
    packedTile65536 2924355840 2924486912 14 5974 54077 31 _ _ (2179633 / 100000) (544909 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2924486912 :
    ThetaLowerSegment 2924486912 2924617984 (58488470908909 / 20000)
      (292455419288723 / 100000) := by
  exact
    packedTile65536 2924486912 2924617984 14 5994 54078 31 _ _ (2179637 / 100000) (54491 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2924617984 :
    ThetaLowerSegment 2924617984 2924749056 (292455419288723 / 100000) (9139638696388 / 3125) := by
  exact
    packedTile65536 2924617984 2924749056 14 5973 54079 31 _ _ (2179641 / 100000) (544911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2924749056 :
    ThetaLowerSegment 2924749056 2924880128 (9139638696388 / 3125) (146240831098349 / 50000) := by
  exact
    packedTile65536 2924749056 2924880128 14 6067 54080 31 _ _ (1089823 / 50000) (2179649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2924880128 :
    ThetaLowerSegment 2924880128 2925011200 (146240831098349 / 50000) (36561861856481 / 12500) := by
  exact
    packedTile65536 2924880128 2925011200 14 6071 54082 31 _ _ (43593 / 2000) (2179653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925011200 :
    ThetaLowerSegment 2925011200 2925142272 (36561861856481 / 12500)
      (292508319346993 / 100000) := by
  exact
    packedTile65536 2925011200 2925142272 14 6159 54083 31 _ _ (435931 / 20000) (1089829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925142272 :
    ThetaLowerSegment 2925142272 2925273344 (292508319346993 / 100000) (9141291281654 / 3125) := by
  exact
    packedTile65536 2925142272 2925273344 14 5965 54084 31 _ _ (2179659 / 100000) (1089831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925273344 :
    ThetaLowerSegment 2925273344 2925404416 (9141291281654 / 3125) (73133653151 / 25) := by
  exact
    packedTile65536 2925273344 2925404416 14 6098 54085 31 _ _ (136229 / 6250) (2179667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925404416 :
    ThetaLowerSegment 2925404416 2925535488 (73133653151 / 25) (73136913389411 / 25000) := by
  exact
    packedTile65536 2925404416 2925535488 14 5983 54087 31 _ _ (544917 / 25000) (2179671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925535488 :
    ThetaLowerSegment 2925535488 2925666560 (73136913389411 / 25000) (73140209054987 / 25000) := by
  exact
    packedTile65536 2925535488 2925666560 14 6048 54088 31 _ _ (2179673 / 100000) (544919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925666560 :
    ThetaLowerSegment 2925666560 2925797632 (73140209054987 / 25000) (2340591331693 / 800) := by
  exact
    packedTile65536 2925666560 2925797632 14 6001 54089 31 _ _ (2179677 / 100000) (13623 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925797632 :
    ThetaLowerSegment 2925797632 2925928704 (2340591331693 / 800) (292586846335249 / 100000) := by
  exact
    packedTile65536 2925797632 2925928704 14 5932 54090 31 _ _ (1089841 / 50000) (435937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2925928704 :
    ThetaLowerSegment 2925928704 2926059776 (292586846335249 / 100000)
      (58519989685559 / 20000) := by
  exact
    packedTile65536 2925928704 2926059776 14 6011 54091 31 _ _ (1089843 / 50000) (2179689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926059776 :
    ThetaLowerSegment 2926059776 2926190848 (58519989685559 / 20000)
      (292613030933177 / 100000) := by
  exact
    packedTile65536 2926059776 2926190848 14 6002 54093 31 _ _ (2179691 / 100000) (1089847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926190848 :
    ThetaLowerSegment 2926190848 2926321920 (292613030933177 / 100000)
      (292626375025967 / 100000) := by
  exact
    packedTile65536 2926190848 2926321920 14 6122 54094 31 _ _ (435939 / 20000) (1089849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926321920 :
    ThetaLowerSegment 2926321920 2926452992 (292626375025967 / 100000)
      (292639527335767 / 100000) := by
  exact
    packedTile65536 2926321920 2926452992 14 6034 54095 31 _ _ (21797 / 1000) (2179703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926452992 :
    ThetaLowerSegment 2926452992 2926584064 (292639527335767 / 100000) (11706104396767 / 4000) := by
  exact
    packedTile65536 2926452992 2926584064 14 6002 54096 31 _ _ (272463 / 12500) (2179707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926584064 :
    ThetaLowerSegment 2926584064 2926715136 (11706104396767 / 4000) (36583221102801 / 12500) := by
  exact
    packedTile65536 2926584064 2926715136 14 6037 54097 31 _ _ (2179709 / 100000) (68116 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926715136 :
    ThetaLowerSegment 2926715136 2926846208 (36583221102801 / 12500) (146339390854509 / 50000) := by
  exact
    packedTile65536 2926715136 2926846208 14 5970 54099 31 _ _ (2179713 / 100000) (544929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926846208 :
    ThetaLowerSegment 2926846208 2926977280 (146339390854509 / 50000) (2926918578373 / 1000) := by
  exact
    packedTile65536 2926846208 2926977280 14 5999 54100 31 _ _ (1089859 / 50000) (2179721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2926977280 :
    ThetaLowerSegment 2926977280 2927108352 (2926918578373 / 1000) (73176286355653 / 25000) := by
  exact
    packedTile65536 2926977280 2927108352 14 6096 54101 31 _ _ (1089861 / 50000) (87189 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2927108352 :
    ThetaLowerSegment 2927108352 2927239424 (73176286355653 / 25000)
      (292718291356149 / 100000) := by
  exact
    packedTile65536 2927108352 2927239424 14 6031 54102 31 _ _ (2179727 / 100000) (217973 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2927239424 :
    ThetaLowerSegment 2927239424 2927370496 (292718291356149 / 100000) (18295711834983 / 6250) := by
  exact
    packedTile65536 2927239424 2927370496 14 6009 54103 31 _ _ (2179731 / 100000) (1089867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2927370496 :
    ThetaLowerSegment 2927370496 2927501568 (18295711834983 / 6250) (9148257397616 / 3125) := by
  exact
    packedTile65536 2927370496 2927501568 14 5894 54105 31 _ _ (272467 / 12500) (2179739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2927501568 :
    ThetaLowerSegment 2927501568 2927632640 (9148257397616 / 3125) (73189379469883 / 25000) := by
  exact
    packedTile65536 2927501568 2927632640 14 6093 54106 31 _ _ (108987 / 5000) (2179743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2927632640 :
    ThetaLowerSegment 2927632640 2927763712 (73189379469883 / 25000) (73192665433963 / 25000) := by
  exact
    packedTile65536 2927632640 2927763712 14 6030 54107 31 _ _ (68117 / 3125) (2179747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2927763712 :
    ThetaLowerSegment 2927763712 2927894784 (73192665433963 / 25000) (29278378818433 / 10000) := by
  exact
    packedTile65536 2927763712 2927894784 14 6022 54108 31 _ _ (2179749 / 100000) (272469 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2927894784 :
    ThetaLowerSegment 2927894784 2928025856 (29278378818433 / 10000)
      (292796934274673 / 100000) := by
  exact
    packedTile65536 2927894784 2928025856 14 6031 54110 31 _ _ (2179753 / 100000) (544939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928025856 :
    ThetaLowerSegment 2928025856 2928156928 (292796934274673 / 100000) (11712397810007 / 4000) := by
  exact
    packedTile65536 2928025856 2928156928 14 5969 54111 31 _ _ (1089879 / 50000) (2179761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928156928 :
    ThetaLowerSegment 2928156928 2928288000 (11712397810007 / 4000) (292822917013837 / 100000) := by
  exact
    packedTile65536 2928156928 2928288000 14 5951 54112 31 _ _ (1089881 / 50000) (435953 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928288000 :
    ThetaLowerSegment 2928288000 2928419072 (292822917013837 / 100000)
      (292836231030673 / 100000) := by
  exact
    packedTile65536 2928288000 2928419072 14 6108 54113 31 _ _ (2179767 / 100000) (217977 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928419072 :
    ThetaLowerSegment 2928419072 2928550144 (292836231030673 / 100000) (18303077085293 / 6250) := by
  exact
    packedTile65536 2928419072 2928550144 14 5965 54114 31 _ _ (2179771 / 100000) (1089887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928550144 :
    ThetaLowerSegment 2928550144 2928681216 (18303077085293 / 6250) (18303893138933 / 6250) := by
  exact
    packedTile65536 2928550144 2928681216 14 5990 54116 31 _ _ (68118 / 3125) (2179779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928681216 :
    ThetaLowerSegment 2928681216 2928812288 (18303893138933 / 6250) (36609421657811 / 12500) := by
  exact
    packedTile65536 2928681216 2928812288 14 6002 54117 31 _ _ (108989 / 5000) (2179783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928812288 :
    ThetaLowerSegment 2928812288 2928943360 (36609421657811 / 12500) (146444254323449 / 50000) := by
  exact
    packedTile65536 2928812288 2928943360 14 6026 54118 31 _ _ (435957 / 20000) (544947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2928943360 :
    ThetaLowerSegment 2928943360 2929074432 (146444254323449 / 50000) (36612732754289 / 12500) := by
  exact
    packedTile65536 2928943360 2929074432 14 6126 54119 31 _ _ (2179789 / 100000) (136237 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929074432 :
    ThetaLowerSegment 2929074432 2929205504 (36612732754289 / 12500) (9153590537576 / 3125) := by
  exact
    packedTile65536 2929074432 2929205504 14 5980 54120 31 _ _ (1089897 / 50000) (2179797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929205504 :
    ThetaLowerSegment 2929205504 2929336576 (9153590537576 / 3125) (146464028321479 / 50000) := by
  exact
    packedTile65536 2929205504 2929336576 14 6037 54122 31 _ _ (1089899 / 50000) (2179801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929336576 :
    ThetaLowerSegment 2929336576 2929467648 (146464028321479 / 50000)
      (292941094044701 / 100000) := by
  exact
    packedTile65536 2929336576 2929467648 14 5981 54123 31 _ _ (2179803 / 100000) (1089903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929467648 :
    ThetaLowerSegment 2929467648 2929598720 (292941094044701 / 100000)
      (58590835449263 / 20000) := by
  exact
    packedTile65536 2929467648 2929598720 14 6002 54124 31 _ _ (2179807 / 100000) (217981 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929598720 :
    ThetaLowerSegment 2929598720 2929729792 (58590835449263 / 20000)
      (292967426143651 / 100000) := by
  exact
    packedTile65536 2929598720 2929729792 14 6078 54125 31 _ _ (544953 / 25000) (435963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929729792 :
    ThetaLowerSegment 2929729792 2929860864 (292967426143651 / 100000)
      (292980537736891 / 100000) := by
  exact
    packedTile65536 2929729792 2929860864 14 6015 54126 31 _ _ (272477 / 12500) (2179819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929860864 :
    ThetaLowerSegment 2929860864 2929991936 (292980537736891 / 100000)
      (292993621022533 / 100000) := by
  exact
    packedTile65536 2929860864 2929991936 14 6002 54128 31 _ _ (2179821 / 100000) (136239 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2929991936 :
    ThetaLowerSegment 2929991936 2930123008 (292993621022533 / 100000)
      (36625833954351 / 12500) := by
  exact
    packedTile65536 2929991936 2930123008 14 5987 54129 31 _ _ (87193 / 4000) (544957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2930123008 :
    ThetaLowerSegment 2930123008 2930254080 (36625833954351 / 12500) (36627479726001 / 12500) := by
  exact
    packedTile65536 2930123008 2930254080 14 6040 54130 31 _ _ (217983 / 10000) (2179833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2930254080 :
    ThetaLowerSegment 2930254080 2930385152 (36627479726001 / 12500) (146516433337913 / 50000) := by
  exact
    packedTile65536 2930254080 2930385152 14 5977 54131 31 _ _ (1089917 / 50000) (2179837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2930385152 :
    ThetaLowerSegment 2930385152 2930516224 (146516433337913 / 50000) (73261442284237 / 25000) := by
  exact
    packedTile65536 2930385152 2930516224 14 5919 54133 31 _ _ (1089919 / 50000) (2179841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2930516224 :
    ThetaLowerSegment 2930516224 2930647296 (73261442284237 / 25000) (36632363653819 / 12500) := by
  exact
    packedTile65536 2930516224 2930647296 14 6028 54134 31 _ _ (2179843 / 100000) (1089923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2930647296 :
    ThetaLowerSegment 2930647296 2930778368 (36632363653819 / 12500) (36633989819681 / 12500) := by
  exact
    packedTile65536 2930647296 2930778368 14 5968 54135 31 _ _ (2179847 / 100000) (43597 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2930778368 :
    ThetaLowerSegment 2930778368 2930909440 (36633989819681 / 12500) (36635647597127 / 12500) := by
  exact
    packedTile65536 2930778368 2930909440 14 6084 54136 31 _ _ (544963 / 25000) (435971 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2930909440 :
    ThetaLowerSegment 2930909440 2931040512 (36635647597127 / 12500) (36637307829953 / 12500) := by
  exact
    packedTile65536 2930909440 2931040512 14 6093 54137 31 _ _ (136241 / 6250) (2179859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931040512 :
    ThetaLowerSegment 2931040512 2931171584 (36637307829953 / 12500)
      (293111526546597 / 100000) := by
  exact
    packedTile65536 2931040512 2931171584 14 5993 54139 31 _ _ (2179861 / 100000) (272483 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931171584 :
    ThetaLowerSegment 2931171584 2931302656 (293111526546597 / 100000)
      (293124653693627 / 100000) := by
  exact
    packedTile65536 2931171584 2931302656 14 6022 54140 31 _ _ (435973 / 20000) (544967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931302656 :
    ThetaLowerSegment 2931302656 2931433728 (293124653693627 / 100000)
      (293137772151287 / 100000) := by
  exact
    packedTile65536 2931302656 2931433728 14 6018 54141 31 _ _ (217987 / 10000) (2179873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931433728 :
    ThetaLowerSegment 2931433728 2931564800 (293137772151287 / 100000)
      (293150962568861 / 100000) := by
  exact
    packedTile65536 2931433728 2931564800 14 6051 54142 31 _ _ (1089937 / 50000) (2179877 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931564800 :
    ThetaLowerSegment 2931564800 2931695872 (293150962568861 / 100000) (14658202201137 / 5000) := by
  exact
    packedTile65536 2931564800 2931695872 14 6001 54143 31 _ _ (2179879 / 100000) (1089941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931695872 :
    ThetaLowerSegment 2931695872 2931826944 (14658202201137 / 5000) (293177038305303 / 100000) := by
  exact
    packedTile65536 2931695872 2931826944 14 5961 54145 31 _ _ (2179883 / 100000) (1089943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931826944 :
    ThetaLowerSegment 2931826944 2931958016 (293177038305303 / 100000)
      (293190285484679 / 100000) := by
  exact
    packedTile65536 2931826944 2931958016 14 6077 54146 31 _ _ (136243 / 6250) (2179891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2931958016 :
    ThetaLowerSegment 2931958016 2932089088 (293190285484679 / 100000)
      (293203345217651 / 100000) := by
  exact
    packedTile65536 2931958016 2932089088 14 5991 54147 31 _ _ (544973 / 25000) (435979 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2932089088 :
    ThetaLowerSegment 2932089088 2932220160 (293203345217651 / 100000)
      (293216367922329 / 100000) := by
  exact
    packedTile65536 2932089088 2932220160 14 5974 54148 31 _ _ (2179897 / 100000) (21799 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2932220160 :
    ThetaLowerSegment 2932220160 2932351232 (293216367922329 / 100000)
      (293229425529319 / 100000) := by
  exact
    packedTile65536 2932220160 2932351232 14 5990 54149 31 _ _ (2179901 / 100000) (68122 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2932351232 :
    ThetaLowerSegment 2932351232 2932482304 (293229425529319 / 100000)
      (293242764374133 / 100000) := by
  exact
    packedTile65536 2932351232 2932482304 14 6119 54151 31 _ _ (1089953 / 50000) (2179909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2932482304 :
    ThetaLowerSegment 2932482304 2932613376 (293242764374133 / 100000)
      (293255922310893 / 100000) := by
  exact
    packedTile65536 2932482304 2932613376 14 6036 54152 31 _ _ (217991 / 10000) (2179913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2932613376 :
    ThetaLowerSegment 2932613376 2932744448 (293255922310893 / 100000)
      (293269110790593 / 100000) := by
  exact
    packedTile65536 2932613376 2932744448 14 6050 54153 31 _ _ (1089957 / 50000) (2179917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2932744448 :
    ThetaLowerSegment 2932744448 2932875520 (293269110790593 / 100000)
      (293282177225079 / 100000) := by
  exact
    packedTile65536 2932744448 2932875520 14 5994 54154 31 _ _ (2179919 / 100000) (1089961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2932875520 :
    ThetaLowerSegment 2932875520 2933006592 (293282177225079 / 100000)
      (293295256763079 / 100000) := by
  exact
    packedTile65536 2932875520 2933006592 14 6000 54156 31 _ _ (2179923 / 100000) (1089963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933006592 :
    ThetaLowerSegment 2933006592 2933137664 (293295256763079 / 100000)
      (293308183736119 / 100000) := by
  exact
    packedTile65536 2933006592 2933137664 14 5930 54157 31 _ _ (272491 / 12500) (2179931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933137664 :
    ThetaLowerSegment 2933137664 2933268736 (293308183736119 / 100000) (2346570682127 / 800) := by
  exact
    packedTile65536 2933137664 2933268736 14 6033 54158 31 _ _ (544983 / 25000) (435987 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933268736 :
    ThetaLowerSegment 2933268736 2933399808 (2346570682127 / 800) (14666719109441 / 5000) := by
  exact
    packedTile65536 2933268736 2933399808 14 5985 54159 31 _ _ (2179937 / 100000) (108997 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933399808 :
    ThetaLowerSegment 2933399808 2933530880 (14666719109441 / 5000) (293347446575233 / 100000) := by
  exact
    packedTile65536 2933399808 2933530880 14 5993 54160 31 _ _ (2179941 / 100000) (272493 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933530880 :
    ThetaLowerSegment 2933530880 2933661952 (293347446575233 / 100000)
      (293360397634419 / 100000) := by
  exact
    packedTile65536 2933530880 2933661952 14 5941 54162 31 _ _ (1089973 / 50000) (2179949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933661952 :
    ThetaLowerSegment 2933661952 2933793024 (293360397634419 / 100000)
      (293373605951469 / 100000) := by
  exact
    packedTile65536 2933661952 2933793024 14 6059 54163 31 _ _ (43599 / 2000) (2179953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933793024 :
    ThetaLowerSegment 2933793024 2933924096 (293373605951469 / 100000)
      (293386663881919 / 100000) := by
  exact
    packedTile65536 2933793024 2933924096 14 5990 54164 31 _ _ (435991 / 20000) (1089979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2933924096 :
    ThetaLowerSegment 2933924096 2934055168 (293386663881919 / 100000)
      (293399922392557 / 100000) := by
  exact
    packedTile65536 2933924096 2934055168 14 6082 54165 31 _ _ (2179959 / 100000) (1089981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934055168 :
    ThetaLowerSegment 2934055168 2934186240 (293399922392557 / 100000)
      (58682586047549 / 20000) := by
  exact
    packedTile65536 2934055168 2934186240 14 5967 54166 31 _ _ (544991 / 25000) (2179967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934186240 :
    ThetaLowerSegment 2934186240 2934317312 (58682586047549 / 20000)
      (293426036205361 / 100000) := by
  exact
    packedTile65536 2934186240 2934317312 14 6012 54168 31 _ _ (68124 / 3125) (2179971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934317312 :
    ThetaLowerSegment 2934317312 2934448384 (293426036205361 / 100000)
      (146719585271343 / 50000) := by
  exact
    packedTile65536 2934317312 2934448384 14 6025 54169 31 _ _ (2179973 / 100000) (272497 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934448384 :
    ThetaLowerSegment 2934448384 2934579456 (146719585271343 / 50000) (58690435693089 / 20000) := by
  exact
    packedTile65536 2934448384 2934579456 14 5967 54170 31 _ _ (2179977 / 100000) (108999 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934579456 :
    ThetaLowerSegment 2934579456 2934710528 (58690435693089 / 20000) (58693095269909 / 20000) := by
  exact
    packedTile65536 2934579456 2934710528 14 6100 54171 31 _ _ (2179981 / 100000) (136249 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934710528 :
    ThetaLowerSegment 2934710528 2934841600 (58693095269909 / 20000)
      (293478667444831 / 100000) := by
  exact
    packedTile65536 2934710528 2934841600 14 6051 54172 31 _ _ (1089993 / 50000) (2179989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934841600 :
    ThetaLowerSegment 2934841600 2934972672 (293478667444831 / 100000)
      (293491838944411 / 100000) := by
  exact
    packedTile65536 2934841600 2934972672 14 6042 54174 31 _ _ (217999 / 10000) (2179993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2934972672 :
    ThetaLowerSegment 2934972672 2935103744 (293491838944411 / 100000)
      (293504892754471 / 100000) := by
  exact
    packedTile65536 2934972672 2935103744 14 5988 54175 31 _ _ (435999 / 20000) (1089999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2935103744 :
    ThetaLowerSegment 2935103744 2935234816 (293504892754471 / 100000)
      (293517950948481 / 100000) := by
  exact
    packedTile65536 2935103744 2935234816 14 5990 54176 31 _ _ (2179999 / 100000) (1090001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2935234816 :
    ThetaLowerSegment 2935234816 2935365888 (293517950948481 / 100000)
      (293531009172441 / 100000) := by
  exact
    packedTile65536 2935234816 2935365888 14 5990 54177 31 _ _ (545001 / 25000) (2180007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2935365888 :
    ThetaLowerSegment 2935365888 2935496960 (293531009172441 / 100000)
      (293544119740553 / 100000) := by
  exact
    packedTile65536 2935365888 2935496960 14 6014 54179 31 _ _ (272501 / 12500) (2180011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2935496960 :
    ThetaLowerSegment 2935496960 2935628032 (293544119740553 / 100000) (9173653978654 / 3125) := by
  exact
    packedTile65536 2935496960 2935628032 14 5875 54180 31 _ _ (2180013 / 100000) (136251 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2935628032 :
    ThetaLowerSegment 2935628032 2935759104 (9173653978654 / 3125) (293570027039081 / 100000) := by
  exact
    packedTile65536 2935628032 2935759104 14 6009 54181 31 _ _ (2180017 / 100000) (109001 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2935759104 :
    ThetaLowerSegment 2935759104 2935890176 (293570027039081 / 100000)
      (293583309913127 / 100000) := by
  exact
    packedTile65536 2935759104 2935890176 14 6093 54182 31 _ _ (1090011 / 50000) (87201 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2935890176 :
    ThetaLowerSegment 2935890176 2936021248 (293583309913127 / 100000)
      (293596313768217 / 100000) := by
  exact
    packedTile65536 2935890176 2936021248 14 5965 54183 31 _ _ (1090013 / 50000) (2180029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936021248 :
    ThetaLowerSegment 2936021248 2936152320 (293596313768217 / 100000)
      (293609289312729 / 100000) := by
  exact
    packedTile65536 2936021248 2936152320 14 5952 54185 31 _ _ (2180031 / 100000) (1090017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936152320 :
    ThetaLowerSegment 2936152320 2936283392 (293609289312729 / 100000)
      (293622583166159 / 100000) := by
  exact
    packedTile65536 2936152320 2936283392 14 6098 54186 31 _ _ (436007 / 20000) (1090019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936283392 :
    ThetaLowerSegment 2936283392 2936414464 (293622583166159 / 100000)
      (293635650325919 / 100000) := by
  exact
    packedTile65536 2936283392 2936414464 14 5994 54187 31 _ _ (54501 / 2500) (2180043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936414464 :
    ThetaLowerSegment 2936414464 2936545536 (293635650325919 / 100000)
      (293648604147367 / 100000) := by
  exact
    packedTile65536 2936414464 2936545536 14 5942 54188 31 _ _ (545011 / 25000) (2180047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936545536 :
    ThetaLowerSegment 2936545536 2936676608 (293648604147367 / 100000)
      (293661780357479 / 100000) := by
  exact
    packedTile65536 2936545536 2936676608 14 6044 54189 31 _ _ (136253 / 6250) (2180051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936676608 :
    ThetaLowerSegment 2936676608 2936807680 (293661780357479 / 100000)
      (293675030719613 / 100000) := by
  exact
    packedTile65536 2936676608 2936807680 14 6078 54191 31 _ _ (2180053 / 100000) (272507 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936807680 :
    ThetaLowerSegment 2936807680 2936938752 (293675030719613 / 100000)
      (29368802603939 / 10000) := by
  exact
    packedTile65536 2936807680 2936938752 14 5961 54192 31 _ _ (2180057 / 100000) (109003 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2936938752 :
    ThetaLowerSegment 2936938752 2937069824 (29368802603939 / 10000) (73425231366561 / 25000) := by
  exact
    packedTile65536 2936938752 2937069824 14 5917 54193 31 _ _ (1090031 / 50000) (436013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937069824 :
    ThetaLowerSegment 2937069824 2937200896 (73425231366561 / 25000) (73428536346617 / 25000) := by
  exact
    packedTile65536 2937069824 2937200896 14 6064 54194 31 _ _ (1090033 / 50000) (2180069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937200896 :
    ThetaLowerSegment 2937200896 2937331968 (73428536346617 / 25000)
      (293727171310693 / 100000) := by
  exact
    packedTile65536 2937200896 2937331968 14 5975 54195 31 _ _ (2180071 / 100000) (1090037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937331968 :
    ThetaLowerSegment 2937331968 2937463040 (293727171310693 / 100000)
      (146870072468509 / 50000) := by
  exact
    packedTile65536 2937331968 2937463040 14 5951 54197 31 _ _ (87203 / 4000) (1090039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937463040 :
    ThetaLowerSegment 2937463040 2937594112 (146870072468509 / 50000)
      (146876638869469 / 50000) := by
  exact
    packedTile65536 2937463040 2937594112 14 6024 54198 31 _ _ (27251 / 1250) (2180083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937594112 :
    ThetaLowerSegment 2937594112 2937725184 (146876638869469 / 50000)
      (146883167131007 / 50000) := by
  exact
    packedTile65536 2937594112 2937725184 14 5989 54199 31 _ _ (545021 / 25000) (2180087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937725184 :
    ThetaLowerSegment 2937725184 2937856256 (146883167131007 / 50000)
      (293779656785893 / 100000) := by
  exact
    packedTile65536 2937725184 2937856256 14 6111 54200 31 _ _ (2180089 / 100000) (545023 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937856256 :
    ThetaLowerSegment 2937856256 2937987328 (293779656785893 / 100000)
      (146896404643481 / 50000) := by
  exact
    packedTile65536 2937856256 2937987328 14 6033 54201 31 _ _ (2180093 / 100000) (68128 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2937987328 :
    ThetaLowerSegment 2937987328 2938118400 (146896404643481 / 50000)
      (146902949297677 / 50000) := by
  exact
    packedTile65536 2937987328 2938118400 14 6004 54203 31 _ _ (1090049 / 50000) (2180101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2938118400 :
    ThetaLowerSegment 2938118400 2938249472 (146902949297677 / 50000)
      (146909507044493 / 50000) := by
  exact
    packedTile65536 2938118400 2938249472 14 6016 54204 31 _ _ (1090051 / 50000) (436021 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2938249472 :
    ThetaLowerSegment 2938249472 2938380544 (146909507044493 / 50000)
      (146916034281857 / 50000) := by
  exact
    packedTile65536 2938249472 2938380544 14 5988 54205 31 _ _ (1090053 / 50000) (2180109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2938380544 :
    ThetaLowerSegment 2938380544 2938511616 (146916034281857 / 50000)
      (293845164490491 / 100000) := by
  exact
    packedTile65536 2938380544 2938511616 14 6007 54206 31 _ _ (2180111 / 100000) (1090057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2938511616 :
    ThetaLowerSegment 2938511616 2938642688 (293845164490491 / 100000)
      (146929136760993 / 50000) := by
  exact
    packedTile65536 2938511616 2938642688 14 6013 54208 31 _ _ (436023 / 20000) (1090059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2938642688 :
    ThetaLowerSegment 2938642688 2938773760 (146929136760993 / 50000)
      (146935668400513 / 50000) := by
  exact
    packedTile65536 2938642688 2938773760 14 5992 54209 31 _ _ (54503 / 2500) (2180123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2938773760 :
    ThetaLowerSegment 2938773760 2938904832 (146935668400513 / 50000)
      (146942200052017 / 50000) := by
  exact
    packedTile65536 2938773760 2938904832 14 5992 54210 31 _ _ (545031 / 25000) (2180127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2938904832 :
    ThetaLowerSegment 2938904832 2939035904 (146942200052017 / 50000) (73474393110863 / 25000) := by
  exact
    packedTile65536 2938904832 2939035904 14 6042 54211 31 _ _ (2180129 / 100000) (545033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939035904 :
    ThetaLowerSegment 2939035904 2939166976 (73474393110863 / 25000) (2939107753289 / 1000) := by
  exact
    packedTile65536 2939035904 2939166976 14 6056 54212 31 _ _ (2180133 / 100000) (272517 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939166976 :
    ThetaLowerSegment 2939166976 2939298048 (2939107753289 / 1000) (146961931348657 / 50000) := by
  exact
    packedTile65536 2939166976 2939298048 14 6003 54214 31 _ _ (1090069 / 50000) (2180141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939298048 :
    ThetaLowerSegment 2939298048 2939429120 (146961931348657 / 50000) (36742117126111 / 12500) := by
  exact
    packedTile65536 2939298048 2939429120 14 5997 54215 31 _ _ (1090071 / 50000) (436029 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939429120 :
    ThetaLowerSegment 2939429120 2939560192 (36742117126111 / 12500) (73487493571987 / 25000) := by
  exact
    packedTile65536 2939429120 2939560192 14 5980 54216 31 _ _ (2180147 / 100000) (43603 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939560192 :
    ThetaLowerSegment 2939560192 2939691264 (73487493571987 / 25000) (14698156247939 / 5000) := by
  exact
    packedTile65536 2939560192 2939691264 14 6032 54217 31 _ _ (2180151 / 100000) (1090077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939691264 :
    ThetaLowerSegment 2939691264 2939822336 (14698156247939 / 5000) (18373524177983 / 6250) := by
  exact
    packedTile65536 2939691264 2939822336 14 6083 54218 31 _ _ (545039 / 25000) (2180159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939822336 :
    ThetaLowerSegment 2939822336 2939953408 (18373524177983 / 6250) (18374348550983 / 6250) := by
  exact
    packedTile65536 2939822336 2939953408 14 6050 54220 31 _ _ (13626 / 625) (2180163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2939953408 :
    ThetaLowerSegment 2939953408 2940084480 (18374348550983 / 6250) (73500673715629 / 25000) := by
  exact
    packedTile65536 2939953408 2940084480 14 6017 54221 31 _ _ (545041 / 25000) (2180167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2940084480 :
    ThetaLowerSegment 2940084480 2940215552 (73500673715629 / 25000) (73504005013861 / 25000) := by
  exact
    packedTile65536 2940084480 2940215552 14 6112 54222 31 _ _ (2180169 / 100000) (545043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2940215552 :
    ThetaLowerSegment 2940215552 2940346624 (73504005013861 / 25000)
      (294029221002959 / 100000) := by
  exact
    packedTile65536 2940215552 2940346624 14 6055 54223 31 _ _ (2180173 / 100000) (136261 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2940346624 :
    ThetaLowerSegment 2940346624 2940477696 (294029221002959 / 100000)
      (294042267188111 / 100000) := by
  exact
    packedTile65536 2940346624 2940477696 14 5984 54224 31 _ _ (1090089 / 50000) (2180181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2940477696 :
    ThetaLowerSegment 2940477696 2940608768 (294042267188111 / 100000)
      (58811101050643 / 20000) := by
  exact
    packedTile65536 2940477696 2940608768 14 6072 54226 31 _ _ (1090091 / 50000) (436037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2940608768 :
    ThetaLowerSegment 2940608768 2940739840 (58811101050643 / 20000)
      (294068730267557 / 100000) := by
  exact
    packedTile65536 2940608768 2940739840 14 6066 54227 31 _ _ (2180187 / 100000) (218019 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2940739840 :
    ThetaLowerSegment 2940739840 2940870912 (294068730267557 / 100000) (11763276642509 / 4000) := by
  exact
    packedTile65536 2940739840 2940870912 14 6048 54228 31 _ _ (2180191 / 100000) (1090097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2940870912 :
    ThetaLowerSegment 2940870912 2941001984 (11763276642509 / 4000) (294095143311857 / 100000) := by
  exact
    packedTile65536 2940870912 2941001984 14 6067 54229 31 _ _ (545049 / 25000) (2180199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941001984 :
    ThetaLowerSegment 2941001984 2941133056 (294095143311857 / 100000)
      (294108244133657 / 100000) := by
  exact
    packedTile65536 2941001984 2941133056 14 6009 54231 31 _ _ (10901 / 500) (2180203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941133056 :
    ThetaLowerSegment 2941133056 2941264128 (294108244133657 / 100000)
      (73530313354223 / 25000) := by
  exact
    packedTile65536 2941133056 2941264128 14 5967 54232 31 _ _ (436041 / 20000) (136263 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941264128 :
    ThetaLowerSegment 2941264128 2941395200 (73530313354223 / 25000) (58826865626053 / 20000) := by
  exact
    packedTile65536 2941264128 2941395200 14 5997 54233 31 _ _ (2180209 / 100000) (545053 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941395200 :
    ThetaLowerSegment 2941395200 2941526272 (58826865626053 / 20000)
      (294147383245709 / 100000) := by
  exact
    packedTile65536 2941395200 2941526272 14 5988 54234 31 _ _ (2180213 / 100000) (272527 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941526272 :
    ThetaLowerSegment 2941526272 2941657344 (294147383245709 / 100000)
      (58832102503701 / 20000) := by
  exact
    packedTile65536 2941526272 2941657344 14 6022 54235 31 _ _ (1090109 / 50000) (2180221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941657344 :
    ThetaLowerSegment 2941657344 2941788416 (58832102503701 / 20000)
      (294173511002069 / 100000) := by
  exact
    packedTile65536 2941657344 2941788416 14 5962 54237 31 _ _ (1090111 / 50000) (87209 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941788416 :
    ThetaLowerSegment 2941788416 2941919488 (294173511002069 / 100000)
      (147093338696461 / 50000) := by
  exact
    packedTile65536 2941788416 2941919488 14 6039 54238 31 _ _ (2180227 / 100000) (218023 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2941919488 :
    ThetaLowerSegment 2941919488 2942050560 (147093338696461 / 50000) (73549934244153 / 25000) := by
  exact
    packedTile65536 2941919488 2942050560 14 5990 54239 31 _ _ (2180231 / 100000) (1090117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942050560 :
    ThetaLowerSegment 2942050560 2942181632 (73549934244153 / 25000) (14710638521371 / 5000) := by
  exact
    packedTile65536 2942050560 2942181632 14 5978 54240 31 _ _ (545059 / 25000) (2180239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942181632 :
    ThetaLowerSegment 2942181632 2942312704 (14710638521371 / 5000) (14711294882623 / 5000) := by
  exact
    packedTile65536 2942181632 2942312704 14 6021 54241 31 _ _ (27253 / 1250) (2180243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942312704 :
    ThetaLowerSegment 2942312704 2942443776 (14711294882623 / 5000) (11769557159073 / 4000) := by
  exact
    packedTile65536 2942312704 2942443776 14 5977 54243 31 _ _ (436049 / 20000) (272531 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942443776 :
    ThetaLowerSegment 2942443776 2942574848 (11769557159073 / 4000) (294251962505347 / 100000) := by
  exact
    packedTile65536 2942443776 2942574848 14 5978 54244 31 _ _ (2180249 / 100000) (545063 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942574848 :
    ThetaLowerSegment 2942574848 2942705920 (294251962505347 / 100000)
      (294265198827381 / 100000) := by
  exact
    packedTile65536 2942574848 2942705920 14 6071 54245 31 _ _ (1090127 / 50000) (2180257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942705920 :
    ThetaLowerSegment 2942705920 2942836992 (294265198827381 / 100000)
      (294278339242347 / 100000) := by
  exact
    packedTile65536 2942705920 2942836992 14 6027 54246 31 _ _ (1090129 / 50000) (2180261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942836992 :
    ThetaLowerSegment 2942836992 2942968064 (294278339242347 / 100000)
      (294291503664303 / 100000) := by
  exact
    packedTile65536 2942836992 2942968064 14 6038 54247 31 _ _ (1090131 / 50000) (436053 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2942968064 :
    ThetaLowerSegment 2942968064 2943099136 (294291503664303 / 100000) (5886089132611 / 2000) := by
  exact
    packedTile65536 2942968064 2943099136 14 5941 54249 31 _ _ (2180267 / 100000) (218027 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2943099136 :
    ThetaLowerSegment 2943099136 2943230208 (5886089132611 / 2000) (58863531634291 / 20000) := by
  exact
    packedTile65536 2943099136 2943230208 14 6055 54250 31 _ _ (2180271 / 100000) (1090137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2943230208 :
    ThetaLowerSegment 2943230208 2943361280 (58863531634291 / 20000) (58866137064111 / 20000) := by
  exact
    packedTile65536 2943230208 2943361280 14 5975 54251 31 _ _ (545069 / 25000) (2180279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2943361280 :
    ThetaLowerSegment 2943361280 2943492352 (58866137064111 / 20000) (58868764301511 / 20000) := by
  exact
    packedTile65536 2943361280 2943492352 14 6025 54252 31 _ _ (54507 / 2500) (2180283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2943492352 :
    ThetaLowerSegment 2943492352 2943623424 (58868764301511 / 20000) (58871382387739 / 20000) := by
  exact
    packedTile65536 2943492352 2943623424 14 6004 54253 31 _ _ (436057 / 20000) (68134 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2943623424 :
    ThetaLowerSegment 2943623424 2943754496 (58871382387739 / 20000) (73592492422379 / 25000) := by
  exact
    packedTile65536 2943623424 2943754496 14 5989 54255 31 _ _ (2180289 / 100000) (545073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2943754496 :
    ThetaLowerSegment 2943754496 2943885568 (73592492422379 / 25000) (147191511554847 / 50000) := by
  exact
    packedTile65536 2943754496 2943885568 14 5987 54256 31 _ _ (1090147 / 50000) (2180297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2943885568 :
    ThetaLowerSegment 2943885568 2944016640 (147191511554847 / 50000)
      (147198100415403 / 50000) := by
  exact
    packedTile65536 2943885568 2944016640 14 6044 54257 31 _ _ (1090149 / 50000) (2180301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944016640 :
    ThetaLowerSegment 2944016640 2944147712 (147198100415403 / 50000)
      (294409358959411 / 100000) := by
  exact
    packedTile65536 2944016640 2944147712 14 6035 54258 31 _ _ (2180303 / 100000) (1090153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944147712 :
    ThetaLowerSegment 2944147712 2944278784 (294409358959411 / 100000)
      (294422405916499 / 100000) := by
  exact
    packedTile65536 2944147712 2944278784 14 5984 54260 31 _ _ (2180307 / 100000) (218031 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944278784 :
    ThetaLowerSegment 2944278784 2944409856 (294422405916499 / 100000) (9201111922996 / 3125) := by
  exact
    packedTile65536 2944278784 2944409856 14 6043 54261 31 _ _ (2180311 / 100000) (1090157 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944409856 :
    ThetaLowerSegment 2944409856 2944540928 (9201111922996 / 3125) (73612186025891 / 25000) := by
  exact
    packedTile65536 2944409856 2944540928 14 6037 54262 31 _ _ (545079 / 25000) (2180319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944540928 :
    ThetaLowerSegment 2944540928 2944672000 (73612186025891 / 25000) (73615461956691 / 25000) := by
  exact
    packedTile65536 2944540928 2944672000 14 6010 54263 31 _ _ (13627 / 625) (2180323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944672000 :
    ThetaLowerSegment 2944672000 2944803072 (73615461956691 / 25000)
      (294474805498239 / 100000) := by
  exact
    packedTile65536 2944672000 2944803072 14 5943 54264 31 _ _ (87213 / 4000) (272541 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944803072 :
    ThetaLowerSegment 2944803072 2944934144 (294474805498239 / 100000)
      (294487686881971 / 100000) := by
  exact
    packedTile65536 2944803072 2944934144 14 5908 54266 31 _ _ (2180329 / 100000) (545083 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2944934144 :
    ThetaLowerSegment 2944934144 2945065216 (294487686881971 / 100000)
      (294500884443673 / 100000) := by
  exact
    packedTile65536 2944934144 2945065216 14 6053 54267 31 _ _ (1090167 / 50000) (2180337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945065216 :
    ThetaLowerSegment 2945065216 2945196288 (294500884443673 / 100000)
      (294514092931277 / 100000) := by
  exact
    packedTile65536 2945065216 2945196288 14 6058 54268 31 _ _ (1090169 / 50000) (2180341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945196288 :
    ThetaLowerSegment 2945196288 2945327360 (294514092931277 / 100000)
      (147263542797607 / 50000) := by
  exact
    packedTile65536 2945196288 2945327360 14 5959 54269 31 _ _ (2180343 / 100000) (1090173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945327360 :
    ThetaLowerSegment 2945327360 2945458432 (147263542797607 / 50000)
      (294540047758129 / 100000) := by
  exact
    packedTile65536 2945327360 2945458432 14 5945 54270 31 _ _ (2180347 / 100000) (43607 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945458432 :
    ThetaLowerSegment 2945458432 2945589504 (294540047758129 / 100000)
      (294553273773361 / 100000) := by
  exact
    packedTile65536 2945458432 2945589504 14 6066 54272 31 _ _ (68136 / 3125) (436071 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945589504 :
    ThetaLowerSegment 2945589504 2945720576 (294553273773361 / 100000)
      (294566464927161 / 100000) := by
  exact
    packedTile65536 2945589504 2945720576 14 6050 54273 31 _ _ (545089 / 25000) (2180359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945720576 :
    ThetaLowerSegment 2945720576 2945851648 (294566464927161 / 100000)
      (294579553628241 / 100000) := by
  exact
    packedTile65536 2945720576 2945851648 14 6003 54274 31 _ _ (54509 / 2500) (2180363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945851648 :
    ThetaLowerSegment 2945851648 2945982720 (294579553628241 / 100000)
      (294592648900431 / 100000) := by
  exact
    packedTile65536 2945851648 2945982720 14 6006 54275 31 _ _ (436073 / 20000) (136273 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2945982720 :
    ThetaLowerSegment 2945982720 2946113792 (294592648900431 / 100000)
      (36825731924433 / 12500) := by
  exact
    packedTile65536 2945982720 2946113792 14 6057 54276 31 _ _ (2180369 / 100000) (545093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946113792 :
    ThetaLowerSegment 2946113792 2946244864 (36825731924433 / 12500) (73654724598183 / 25000) := by
  exact
    packedTile65536 2946113792 2946244864 14 5982 54278 31 _ _ (1090187 / 50000) (2180377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946244864 :
    ThetaLowerSegment 2946244864 2946375936 (73654724598183 / 25000) (9207250077016 / 3125) := by
  exact
    packedTile65536 2946244864 2946375936 14 6010 54279 31 _ _ (1090189 / 50000) (2180381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946375936 :
    ThetaLowerSegment 2946375936 2946507008 (9207250077016 / 3125) (147322540200873 / 50000) := by
  exact
    packedTile65536 2946375936 2946507008 14 5998 54280 31 _ _ (2180383 / 100000) (1090193 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946507008 :
    ThetaLowerSegment 2946507008 2946638080 (147322540200873 / 50000)
      (147328981064071 / 50000) := by
  exact
    packedTile65536 2946507008 2946638080 14 5908 54281 31 _ _ (2180387 / 100000) (218039 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946638080 :
    ThetaLowerSegment 2946638080 2946769152 (147328981064071 / 50000)
      (147335614906731 / 50000) := by
  exact
    packedTile65536 2946638080 2946769152 14 6085 54282 31 _ _ (272549 / 12500) (436079 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946769152 :
    ThetaLowerSegment 2946769152 2946900224 (147335614906731 / 50000)
      (147342161545721 / 50000) := by
  exact
    packedTile65536 2946769152 2946900224 14 6005 54284 31 _ _ (545099 / 25000) (2180399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2946900224 :
    ThetaLowerSegment 2946900224 2947031296 (147342161545721 / 50000)
      (147348710377121 / 50000) := by
  exact
    packedTile65536 2946900224 2947031296 14 6007 54285 31 _ _ (5451 / 250) (2180403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947031296 :
    ThetaLowerSegment 2947031296 2947162368 (147348710377121 / 50000)
      (294710501003837 / 100000) := by
  exact
    packedTile65536 2947031296 2947162368 14 5999 54286 31 _ _ (436081 / 20000) (272551 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947162368 :
    ThetaLowerSegment 2947162368 2947293440 (294710501003837 / 100000)
      (294723788416283 / 100000) := by
  exact
    packedTile65536 2947162368 2947293440 14 6094 54287 31 _ _ (2180409 / 100000) (545103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947293440 :
    ThetaLowerSegment 2947293440 2947424512 (294723788416283 / 100000)
      (294736881802353 / 100000) := by
  exact
    packedTile65536 2947293440 2947424512 14 6005 54288 31 _ _ (1090207 / 50000) (2180417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947424512 :
    ThetaLowerSegment 2947424512 2947555584 (294736881802353 / 100000)
      (294750127841703 / 100000) := by
  exact
    packedTile65536 2947424512 2947555584 14 6075 54290 31 _ _ (1090209 / 50000) (2180421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947555584 :
    ThetaLowerSegment 2947555584 2947686656 (294750127841703 / 100000)
      (58952639459433 / 20000) := by
  exact
    packedTile65536 2947555584 2947686656 14 5994 54291 31 _ _ (2180423 / 100000) (1090213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947686656 :
    ThetaLowerSegment 2947686656 2947817728 (58952639459433 / 20000)
      (294776428128201 / 100000) := by
  exact
    packedTile65536 2947686656 2947817728 14 6068 54292 31 _ _ (2180427 / 100000) (218043 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947817728 :
    ThetaLowerSegment 2947817728 2947948800 (294776428128201 / 100000)
      (294789467111561 / 100000) := by
  exact
    packedTile65536 2947817728 2947948800 14 5980 54293 31 _ _ (136277 / 6250) (436087 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2947948800 :
    ThetaLowerSegment 2947948800 2948079872 (294789467111561 / 100000)
      (58960494246373 / 20000) := by
  exact
    packedTile65536 2947948800 2948079872 14 5964 54295 31 _ _ (545109 / 25000) (2180439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948079872 :
    ThetaLowerSegment 2948079872 2948210944 (58960494246373 / 20000) (58963108593933 / 20000) := by
  exact
    packedTile65536 2948079872 2948210944 14 5995 54296 31 _ _ (54511 / 2500) (2180443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948210944 :
    ThetaLowerSegment 2948210944 2948342016 (58963108593933 / 20000) (14741432917317 / 5000) := by
  exact
    packedTile65536 2948210944 2948342016 14 6015 54297 31 _ _ (436089 / 20000) (68139 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948342016 :
    ThetaLowerSegment 2948342016 2948473088 (14741432917317 / 5000) (147420916309599 / 50000) := by
  exact
    packedTile65536 2948342016 2948473088 14 6042 54298 31 _ _ (2180449 / 100000) (545113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948473088 :
    ThetaLowerSegment 2948473088 2948604160 (147420916309599 / 50000)
      (147427516543857 / 50000) := by
  exact
    packedTile65536 2948473088 2948604160 14 6054 54299 31 _ _ (1090227 / 50000) (2180457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948604160 :
    ThetaLowerSegment 2948604160 2948735232 (147427516543857 / 50000) (36858507665533 / 12500) := by
  exact
    packedTile65536 2948604160 2948735232 14 5975 54301 31 _ _ (1090229 / 50000) (2180461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948735232 :
    ThetaLowerSegment 2948735232 2948866304 (36858507665533 / 12500) (147440539344187 / 50000) := by
  exact
    packedTile65536 2948735232 2948866304 14 5970 54302 31 _ _ (2180463 / 100000) (1090233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948866304 :
    ThetaLowerSegment 2948866304 2948997376 (147440539344187 / 50000) (58978824884487 / 20000) := by
  exact
    packedTile65536 2948866304 2948997376 14 5983 54303 31 _ _ (2180467 / 100000) (218047 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2948997376 :
    ThetaLowerSegment 2948997376 2949128448 (58978824884487 / 20000)
      (294907368609363 / 100000) := by
  exact
    packedTile65536 2948997376 2949128448 14 6074 54304 31 _ _ (272559 / 12500) (87219 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2949128448 :
    ThetaLowerSegment 2949128448 2949259520 (294907368609363 / 100000)
      (294920556128211 / 100000) := by
  exact
    packedTile65536 2949128448 2949259520 14 6048 54305 31 _ _ (545119 / 25000) (2180479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2949259520 :
    ThetaLowerSegment 2949259520 2949390592 (294920556128211 / 100000)
      (294933562691411 / 100000) := by
  exact
    packedTile65536 2949259520 2949390592 14 5965 54307 31 _ _ (13628 / 625) (2180483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2949390592 :
    ThetaLowerSegment 2949390592 2949521664 (294933562691411 / 100000)
      (36868357138557 / 12500) := by
  exact
    packedTile65536 2949390592 2949521664 14 6097 54308 31 _ _ (436097 / 20000) (272561 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2949521664 :
    ThetaLowerSegment 2949521664 2949652736 (36868357138557 / 12500) (73739991552081 / 25000) := by
  exact
    packedTile65536 2949521664 2949652736 14 6012 54309 31 _ _ (2180489 / 100000) (545123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2949652736 :
    ThetaLowerSegment 2949652736 2949783808 (73739991552081 / 25000) (147486564925301 / 50000) := by
  exact
    packedTile65536 2949652736 2949783808 14 6037 54310 31 _ _ (1090247 / 50000) (2180497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2949783808 :
    ThetaLowerSegment 2949783808 2949914880 (147486564925301 / 50000) (36873276332263 / 12500) := by
  exact
    packedTile65536 2949783808 2949914880 14 5999 54311 31 _ _ (1090249 / 50000) (2180501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2949914880 :
    ThetaLowerSegment 2949914880 2950045952 (36873276332263 / 12500)
      (294999160665421 / 100000) := by
  exact
    packedTile65536 2949914880 2950045952 14 5939 54313 31 _ _ (2180503 / 100000) (1090253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950045952 :
    ThetaLowerSegment 2950045952 2950177024 (294999160665421 / 100000)
      (295012418147981 / 100000) := by
  exact
    packedTile65536 2950045952 2950177024 14 6080 54314 31 _ _ (2180507 / 100000) (218051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950177024 :
    ThetaLowerSegment 2950177024 2950308096 (295012418147981 / 100000)
      (295025529566637 / 100000) := by
  exact
    packedTile65536 2950177024 2950308096 14 6013 54315 31 _ _ (68141 / 3125) (436103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950308096 :
    ThetaLowerSegment 2950308096 2950439168 (295025529566637 / 100000)
      (295038798006497 / 100000) := by
  exact
    packedTile65536 2950308096 2950439168 14 6085 54316 31 _ _ (545129 / 25000) (2180519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950439168 :
    ThetaLowerSegment 2950439168 2950570240 (295038798006497 / 100000)
      (295051828794017 / 100000) := by
  exact
    packedTile65536 2950439168 2950570240 14 5976 54317 31 _ _ (54513 / 2500) (2180523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950570240 :
    ThetaLowerSegment 2950570240 2950701312 (295051828794017 / 100000)
      (147532417812821 / 50000) := by
  exact
    packedTile65536 2950570240 2950701312 14 5965 54319 31 _ _ (87221 / 4000) (136283 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950701312 :
    ThetaLowerSegment 2950701312 2950832384 (147532417812821 / 50000)
      (295078008201331 / 100000) := by
  exact
    packedTile65536 2950701312 2950832384 14 6041 54320 31 _ _ (2180529 / 100000) (545133 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950832384 :
    ThetaLowerSegment 2950832384 2950963456 (295078008201331 / 100000)
      (295090901698873 / 100000) := by
  exact
    packedTile65536 2950832384 2950963456 14 5913 54321 31 _ _ (1090267 / 50000) (2180537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2950963456 :
    ThetaLowerSegment 2950963456 2951094528 (295090901698873 / 100000)
      (295104083051083 / 100000) := by
  exact
    packedTile65536 2950963456 2951094528 14 6045 54322 31 _ _ (1090269 / 50000) (2180541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2951094528 :
    ThetaLowerSegment 2951094528 2951225600 (295104083051083 / 100000)
      (147558514467437 / 50000) := by
  exact
    packedTile65536 2951094528 2951225600 14 5937 54323 31 _ _ (2180543 / 100000) (1090273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2951225600 :
    ThetaLowerSegment 2951225600 2951356672 (147558514467437 / 50000) (29513030410501 / 10000) := by
  exact
    packedTile65536 2951225600 2951356672 14 6088 54325 31 _ _ (2180547 / 100000) (43611 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2951356672 :
    ThetaLowerSegment 2951356672 2951487744 (29513030410501 / 10000) (147571686076573 / 50000) := by
  exact
    packedTile65536 2951356672 2951487744 14 5993 54326 31 _ _ (272569 / 12500) (436111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2951487744 :
    ThetaLowerSegment 2951487744 2951618816 (147571686076573 / 50000)
      (147578238647353 / 50000) := by
  exact
    packedTile65536 2951487744 2951618816 14 6010 54327 31 _ _ (545139 / 25000) (2180559 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2951618816 :
    ThetaLowerSegment 2951618816 2951749888 (147578238647353 / 50000)
      (147584807584353 / 50000) := by
  exact
    packedTile65536 2951618816 2951749888 14 6025 54328 31 _ _ (27257 / 1250) (2180563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2951749888 :
    ThetaLowerSegment 2951749888 2951880960 (147584807584353 / 50000)
      (295182787961871 / 100000) := by
  exact
    packedTile65536 2951749888 2951880960 14 6041 54330 31 _ _ (436113 / 20000) (272571 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2951880960 :
    ThetaLowerSegment 2951880960 2952012032 (295182787961871 / 100000)
      (59039194336409 / 20000) := by
  exact
    packedTile65536 2951880960 2952012032 14 6046 54331 31 _ _ (2180569 / 100000) (545143 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952012032 :
    ThetaLowerSegment 2952012032 2952143104 (59039194336409 / 20000) (11808363949501 / 4000) := by
  exact
    packedTile65536 2952012032 2952143104 14 6020 54332 31 _ _ (1090287 / 50000) (2180577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952143104 :
    ThetaLowerSegment 2952143104 2952274176 (11808363949501 / 4000) (59044445163417 / 20000) := by
  exact
    packedTile65536 2952143104 2952274176 14 6020 54333 31 _ _ (1090289 / 50000) (2180581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952274176 :
    ThetaLowerSegment 2952274176 2952405248 (59044445163417 / 20000)
      (295235296231587 / 100000) := by
  exact
    packedTile65536 2952274176 2952405248 14 5994 54334 31 _ _ (2180583 / 100000) (1090293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952405248 :
    ThetaLowerSegment 2952405248 2952536320 (295235296231587 / 100000) (11809937283507 / 4000) := by
  exact
    packedTile65536 2952405248 2952536320 14 6024 54336 31 _ _ (2180587 / 100000) (218059 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952536320 :
    ThetaLowerSegment 2952536320 2952667392 (11809937283507 / 4000) (295261539626187 / 100000) := by
  exact
    packedTile65536 2952536320 2952667392 14 6011 54337 31 _ _ (136287 / 6250) (436119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952667392 :
    ThetaLowerSegment 2952667392 2952798464 (295261539626187 / 100000)
      (59054906323431 / 20000) := by
  exact
    packedTile65536 2952667392 2952798464 14 5958 54338 31 _ _ (545149 / 25000) (2180599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952798464 :
    ThetaLowerSegment 2952798464 2952929536 (59054906323431 / 20000) (59057562730351 / 20000) := by
  exact
    packedTile65536 2952798464 2952929536 14 6091 54339 31 _ _ (10903 / 500) (2180603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2952929536 :
    ThetaLowerSegment 2952929536 2953060608 (59057562730351 / 20000) (29530083404421 / 10000) := by
  exact
    packedTile65536 2952929536 2953060608 14 5971 54340 31 _ _ (436121 / 20000) (68144 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953060608 :
    ThetaLowerSegment 2953060608 2953191680 (29530083404421 / 10000) (7382847397303 / 2500) := by
  exact
    packedTile65536 2953060608 2953191680 14 5990 54342 31 _ _ (2180609 / 100000) (545153 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953191680 :
    ThetaLowerSegment 2953191680 2953322752 (7382847397303 / 2500) (147663392750737 / 50000) := by
  exact
    packedTile65536 2953191680 2953322752 14 5911 54343 31 _ _ (1090307 / 50000) (2180617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953322752 :
    ThetaLowerSegment 2953322752 2953339136 (147663392750737 / 50000)
      (147664199579397 / 50000) := by
  exact
    packedTile65536 2953322752 2953339136 11 740 54344 31 _ _ (1090309 / 50000) (2180621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2953339136 :
    ThetaLowerSegment 2953339136 2953341184 (147664199579397 / 50000)
      (295328588872647 / 100000) := by
  exact
    packedTile65536 2953339136 2953341184 8 87 54344 31 _ _ (2180619 / 100000) (1090311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2921341184_2953341184 :
    ThetaLowerSegment 2921341184 2953341184 (14606402076837 / 5000) (295328588872647 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2921341184 cell2921472256)
                  (ThetaLowerSegment.join cell2921603328 cell2921734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2921865472 cell2921996544)
                  (ThetaLowerSegment.join cell2922127616 cell2922258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2922389760 cell2922520832)
                  (ThetaLowerSegment.join cell2922651904 cell2922782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2922914048 cell2923045120)
                  (ThetaLowerSegment.join cell2923176192 cell2923307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2923438336 cell2923569408)
                  (ThetaLowerSegment.join cell2923700480 cell2923831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2923962624 cell2924093696)
                  (ThetaLowerSegment.join cell2924224768 cell2924355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2924486912 cell2924617984)
                  (ThetaLowerSegment.join cell2924749056 cell2924880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2925011200 cell2925142272)
                  (ThetaLowerSegment.join cell2925273344 cell2925404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2925535488 cell2925666560)
                  (ThetaLowerSegment.join cell2925797632 cell2925928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2926059776 cell2926190848)
                  (ThetaLowerSegment.join cell2926321920 cell2926452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2926584064 cell2926715136)
                  (ThetaLowerSegment.join cell2926846208 cell2926977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2927108352 cell2927239424)
                  (ThetaLowerSegment.join cell2927370496 cell2927501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2927632640 cell2927763712)
                  (ThetaLowerSegment.join cell2927894784 cell2928025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2928156928 cell2928288000)
                  (ThetaLowerSegment.join cell2928419072 cell2928550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2928681216 cell2928812288)
                  (ThetaLowerSegment.join cell2928943360 cell2929074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2929205504 cell2929336576)
                  (ThetaLowerSegment.join cell2929467648 cell2929598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2929729792 cell2929860864)
                  (ThetaLowerSegment.join cell2929991936 cell2930123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2930254080 cell2930385152)
                  (ThetaLowerSegment.join cell2930516224 cell2930647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2930778368 cell2930909440)
                  (ThetaLowerSegment.join cell2931040512 cell2931171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2931302656 cell2931433728)
                  (ThetaLowerSegment.join cell2931564800 cell2931695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2931826944 cell2931958016)
                  (ThetaLowerSegment.join cell2932089088 cell2932220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2932351232 cell2932482304)
                  (ThetaLowerSegment.join cell2932613376 cell2932744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2932875520 cell2933006592)
                  (ThetaLowerSegment.join cell2933137664 cell2933268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2933399808 cell2933530880)
                  (ThetaLowerSegment.join cell2933661952 cell2933793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2933924096 cell2934055168)
                  (ThetaLowerSegment.join cell2934186240 cell2934317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2934448384 cell2934579456)
                  (ThetaLowerSegment.join cell2934710528 cell2934841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2934972672 cell2935103744)
                  (ThetaLowerSegment.join cell2935234816 cell2935365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2935496960 cell2935628032)
                  (ThetaLowerSegment.join cell2935759104 cell2935890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2936021248 cell2936152320)
                  (ThetaLowerSegment.join cell2936283392 cell2936414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2936545536 cell2936676608)
                  (ThetaLowerSegment.join cell2936807680 cell2936938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2937069824 cell2937200896)
                  (ThetaLowerSegment.join cell2937331968 cell2937463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2937594112 cell2937725184)
                  (ThetaLowerSegment.join cell2937856256 cell2937987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2938118400 cell2938249472)
                  (ThetaLowerSegment.join cell2938380544 cell2938511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2938642688 cell2938773760)
                  (ThetaLowerSegment.join cell2938904832 cell2939035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2939166976 cell2939298048)
                  (ThetaLowerSegment.join cell2939429120 cell2939560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2939691264 cell2939822336)
                  (ThetaLowerSegment.join cell2939953408 cell2940084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2940215552 cell2940346624)
                  (ThetaLowerSegment.join cell2940477696 cell2940608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2940739840 cell2940870912)
                  (ThetaLowerSegment.join cell2941001984 cell2941133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2941264128 cell2941395200)
                  (ThetaLowerSegment.join cell2941526272 cell2941657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2941788416 cell2941919488)
                  (ThetaLowerSegment.join cell2942050560 cell2942181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2942312704 cell2942443776)
                  (ThetaLowerSegment.join cell2942574848 cell2942705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2942836992 cell2942968064)
                  (ThetaLowerSegment.join cell2943099136 cell2943230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2943361280 cell2943492352)
                  (ThetaLowerSegment.join cell2943623424 cell2943754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2943885568 cell2944016640)
                  (ThetaLowerSegment.join cell2944147712 cell2944278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2944409856 cell2944540928)
                  (ThetaLowerSegment.join cell2944672000 cell2944803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2944934144 cell2945065216)
                  (ThetaLowerSegment.join cell2945196288 cell2945327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2945458432 cell2945589504)
                  (ThetaLowerSegment.join cell2945720576 cell2945851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2945982720 cell2946113792)
                  (ThetaLowerSegment.join cell2946244864 cell2946375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2946507008 cell2946638080)
                  (ThetaLowerSegment.join cell2946769152 cell2946900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2947031296 cell2947162368)
                  (ThetaLowerSegment.join cell2947293440 cell2947424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2947555584 cell2947686656)
                  (ThetaLowerSegment.join cell2947817728 cell2947948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2948079872 cell2948210944)
                  (ThetaLowerSegment.join cell2948342016 cell2948473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2948604160 cell2948735232)
                  (ThetaLowerSegment.join cell2948866304 cell2948997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2949128448 cell2949259520)
                  (ThetaLowerSegment.join cell2949390592 cell2949521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2949652736 cell2949783808)
                  (ThetaLowerSegment.join cell2949914880 cell2950045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2950177024 cell2950308096)
                  (ThetaLowerSegment.join cell2950439168 cell2950570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2950701312 cell2950832384)
                  (ThetaLowerSegment.join cell2950963456 cell2951094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2951225600 cell2951356672)
                  (ThetaLowerSegment.join cell2951487744 cell2951618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2951749888 cell2951880960)
                  (ThetaLowerSegment.join cell2952012032 cell2952143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2952274176 cell2952405248)
                  (ThetaLowerSegment.join cell2952536320 cell2952667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2952798464 cell2952929536)
                (ThetaLowerSegment.join cell2953060608 cell2953191680))
              (ThetaLowerSegment.join cell2953322752 cell2953339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
