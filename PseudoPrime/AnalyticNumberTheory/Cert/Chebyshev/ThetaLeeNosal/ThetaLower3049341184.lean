/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3049341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3017341184 :
    ThetaLowerSegment 3017341184 3017472256 (301726405592907 / 100000) (9429364831537 / 3125) := by
  exact
    packedTile65536 3017341184 3017472256 14 6079 54930 31 _ _ (2182763 / 100000) (1091383 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017472256 :
    ThetaLowerSegment 3017472256 3017603328 (9429364831537 / 3125) (301752707910941 / 100000) := by
  exact
    packedTile65536 3017472256 3017603328 14 5971 54931 31 _ _ (2182767 / 100000) (218277 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017603328 :
    ThetaLowerSegment 3017603328 3017734400 (301752707910941 / 100000)
      (301765839461277 / 100000) := by
  exact
    packedTile65536 3017603328 3017734400 14 6016 54932 31 _ _ (2182771 / 100000) (1091387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017734400 :
    ThetaLowerSegment 3017734400 3017865472 (301765839461277 / 100000)
      (301778966676141 / 100000) := by
  exact
    packedTile65536 3017734400 3017865472 14 6014 54933 31 _ _ (272847 / 12500) (2182779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017865472 :
    ThetaLowerSegment 3017865472 3017996544 (301778966676141 / 100000)
      (301792048076681 / 100000) := by
  exact
    packedTile65536 3017865472 3017996544 14 5993 54935 31 _ _ (109139 / 5000) (2182783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3017996544 :
    ThetaLowerSegment 3017996544 3018127616 (301792048076681 / 100000)
      (301805218995337 / 100000) := by
  exact
    packedTile65536 3017996544 3018127616 14 6034 54936 31 _ _ (68212 / 3125) (2182787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3018127616 :
    ThetaLowerSegment 3018127616 3018258688 (301805218995337 / 100000)
      (301818193493153 / 100000) := by
  exact
    packedTile65536 3018127616 3018258688 14 5944 54937 31 _ _ (2182789 / 100000) (272849 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3018258688 :
    ThetaLowerSegment 3018258688 3018389760 (301818193493153 / 100000)
      (60366268527637 / 20000) := by
  exact
    packedTile65536 3018258688 3018389760 14 6024 54938 31 _ _ (2182793 / 100000) (545699 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3018389760 :
    ThetaLowerSegment 3018389760 3018520832 (60366268527637 / 20000)
      (301844391398651 / 100000) := by
  exact
    packedTile65536 3018389760 3018520832 14 5978 54939 31 _ _ (2182797 / 100000) (5457 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3018520832 :
    ThetaLowerSegment 3018520832 3018651904 (301844391398651 / 100000)
      (301857540597899 / 100000) := by
  exact
    packedTile65536 3018520832 3018651904 14 6024 54941 31 _ _ (1091401 / 50000) (436561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3018651904 :
    ThetaLowerSegment 3018651904 3018782976 (301857540597899 / 100000)
      (301870637433899 / 100000) := by
  exact
    packedTile65536 3018651904 3018782976 14 6000 54942 31 _ _ (1091403 / 50000) (2182809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3018782976 :
    ThetaLowerSegment 3018782976 3018914048 (301870637433899 / 100000)
      (301883767036049 / 100000) := by
  exact
    packedTile65536 3018782976 3018914048 14 6015 54943 31 _ _ (218281 / 10000) (2182813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3018914048 :
    ThetaLowerSegment 3018914048 3019045120 (301883767036049 / 100000)
      (150948374118427 / 50000) := by
  exact
    packedTile65536 3018914048 3019045120 14 5947 54944 31 _ _ (436563 / 20000) (1091409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019045120 :
    ThetaLowerSegment 3019045120 3019176192 (150948374118427 / 50000)
      (301909899721329 / 100000) := by
  exact
    packedTile65536 3019045120 3019176192 14 6025 54945 31 _ _ (2182819 / 100000) (1091411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019176192 :
    ThetaLowerSegment 3019176192 3019307264 (301909899721329 / 100000)
      (301922896249471 / 100000) := by
  exact
    packedTile65536 3019176192 3019307264 14 5954 54947 31 _ _ (2182823 / 100000) (1091413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019307264 :
    ThetaLowerSegment 3019307264 3019438336 (301922896249471 / 100000)
      (301936069616451 / 100000) := by
  exact
    packedTile65536 3019307264 3019438336 14 6035 54948 31 _ _ (545707 / 25000) (2182831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019438336 :
    ThetaLowerSegment 3019438336 3019569408 (301936069616451 / 100000)
      (301949256104563 / 100000) := by
  exact
    packedTile65536 3019438336 3019569408 14 6041 54949 31 _ _ (136427 / 6250) (436567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019569408 :
    ThetaLowerSegment 3019569408 3019700480 (301949256104563 / 100000)
      (150981158009167 / 50000) := by
  exact
    packedTile65536 3019569408 3019700480 14 5983 54950 31 _ _ (2182837 / 100000) (54571 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019700480 :
    ThetaLowerSegment 3019700480 3019831552 (150981158009167 / 50000) (60395078683753 / 20000) := by
  exact
    packedTile65536 3019700480 3019831552 14 5991 54951 31 _ _ (2182841 / 100000) (545711 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019831552 :
    ThetaLowerSegment 3019831552 3019962624 (60395078683753 / 20000) (7549711771079 / 2500) := by
  exact
    packedTile65536 3019831552 3019962624 14 5991 54952 31 _ _ (436569 / 20000) (68214 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3019962624 :
    ThetaLowerSegment 3019962624 3020093696 (7549711771079 / 2500) (7550045310559 / 2500) := by
  exact
    packedTile65536 3019962624 3020093696 14 6112 54954 31 _ _ (43657 / 2000) (2182853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3020093696 :
    ThetaLowerSegment 3020093696 3020224768 (7550045310559 / 2500) (151007473327439 / 50000) := by
  exact
    packedTile65536 3020093696 3020224768 14 6017 54955 31 _ _ (1091427 / 50000) (2182857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3020224768 :
    ThetaLowerSegment 3020224768 3020355840 (151007473327439 / 50000) (75507016953579 / 25000) := by
  exact
    packedTile65536 3020224768 3020355840 14 6011 54956 31 _ _ (1091429 / 50000) (2182861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3020355840 :
    ThetaLowerSegment 3020355840 3020486912 (75507016953579 / 25000) (151020567216117 / 50000) := by
  exact
    packedTile65536 3020355840 3020486912 14 5986 54957 31 _ _ (2182863 / 100000) (1091433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3020486912 :
    ThetaLowerSegment 3020486912 3020617984 (151020567216117 / 50000)
      (151027107085649 / 50000) := by
  exact
    packedTile65536 3020486912 3020617984 14 5992 54958 31 _ _ (2182867 / 100000) (218287 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3020617984 :
    ThetaLowerSegment 3020617984 3020749056 (151027107085649 / 50000) (75516826757889 / 25000) := by
  exact
    packedTile65536 3020617984 3020749056 14 5998 54960 31 _ _ (2182871 / 100000) (1091437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3020749056 :
    ThetaLowerSegment 3020749056 3020880128 (75516826757889 / 25000) (75520085791757 / 25000) := by
  exact
    packedTile65536 3020749056 3020880128 14 5972 54961 31 _ _ (545719 / 25000) (2182879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3020880128 :
    ThetaLowerSegment 3020880128 3021011200 (75520085791757 / 25000) (75523381940557 / 25000) := by
  exact
    packedTile65536 3020880128 3021011200 14 6040 54962 31 _ _ (13643 / 625) (2182883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021011200 :
    ThetaLowerSegment 3021011200 3021142272 (75523381940557 / 25000) (75526625706181 / 25000) := by
  exact
    packedTile65536 3021011200 3021142272 14 5944 54963 31 _ _ (545721 / 25000) (2182887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021142272 :
    ThetaLowerSegment 3021142272 3021273344 (75526625706181 / 25000)
      (302119637267837 / 100000) := by
  exact
    packedTile65536 3021142272 3021273344 14 6017 54964 31 _ _ (2182889 / 100000) (545723 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021273344 :
    ThetaLowerSegment 3021273344 3021404416 (302119637267837 / 100000)
      (302132542531253 / 100000) := by
  exact
    packedTile65536 3021273344 3021404416 14 5912 54966 31 _ _ (2182893 / 100000) (136431 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021404416 :
    ThetaLowerSegment 3021404416 3021535488 (302132542531253 / 100000)
      (151072847242839 / 50000) := by
  exact
    packedTile65536 3021404416 3021535488 14 6025 54967 31 _ _ (2182897 / 100000) (21829 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021535488 :
    ThetaLowerSegment 3021535488 3021666560 (151072847242839 / 50000) (30215880499509 / 10000) := by
  exact
    packedTile65536 3021535488 3021666560 14 6006 54968 31 _ _ (1091451 / 50000) (436581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021666560 :
    ThetaLowerSegment 3021666560 3021797632 (30215880499509 / 10000) (37771496262647 / 12500) := by
  exact
    packedTile65536 3021666560 3021797632 14 6031 54969 31 _ _ (1091453 / 50000) (2182909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021797632 :
    ThetaLowerSegment 3021797632 3021928704 (37771496262647 / 12500) (75546274530479 / 25000) := by
  exact
    packedTile65536 3021797632 3021928704 14 6014 54970 31 _ _ (218291 / 10000) (2182913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3021928704 :
    ThetaLowerSegment 3021928704 3022059776 (75546274530479 / 25000)
      (302198110478231 / 100000) := by
  exact
    packedTile65536 3021928704 3022059776 14 5961 54972 31 _ _ (436583 / 20000) (1091459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022059776 :
    ThetaLowerSegment 3022059776 3022190848 (302198110478231 / 100000)
      (75552812366923 / 25000) := by
  exact
    packedTile65536 3022059776 3022190848 14 6019 54973 31 _ _ (2182919 / 100000) (1091461 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022190848 :
    ThetaLowerSegment 3022190848 3022321920 (75552812366923 / 25000) (151112175685769 / 50000) := by
  exact
    packedTile65536 3022190848 3022321920 14 6002 54974 31 _ _ (2182923 / 100000) (1091463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022321920 :
    ThetaLowerSegment 3022321920 3022452992 (151112175685769 / 50000)
      (151118791049073 / 50000) := by
  exact
    packedTile65536 3022321920 3022452992 14 6061 54975 31 _ _ (136433 / 6250) (2182931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022452992 :
    ThetaLowerSegment 3022452992 3022584064 (151118791049073 / 50000)
      (151125318015753 / 50000) := by
  exact
    packedTile65536 3022452992 3022584064 14 5980 54976 31 _ _ (545733 / 25000) (436587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022584064 :
    ThetaLowerSegment 3022584064 3022715136 (151125318015753 / 50000)
      (151131851543201 / 50000) := by
  exact
    packedTile65536 3022584064 3022715136 14 5986 54978 31 _ _ (272867 / 12500) (2182939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022715136 :
    ThetaLowerSegment 3022715136 3022846208 (151131851543201 / 50000)
      (151138334877971 / 50000) := by
  exact
    packedTile65536 3022715136 3022846208 14 5940 54979 31 _ _ (2182941 / 100000) (68217 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022846208 :
    ThetaLowerSegment 3022846208 3022977280 (151138334877971 / 50000)
      (302290070855297 / 100000) := by
  exact
    packedTile65536 3022846208 3022977280 14 6139 54980 31 _ _ (436589 / 20000) (545737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3022977280 :
    ThetaLowerSegment 3022977280 3023108352 (302290070855297 / 100000)
      (60460604021753 / 20000) := by
  exact
    packedTile65536 3022977280 3023108352 14 5932 54981 31 _ _ (2182949 / 100000) (272869 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3023108352 :
    ThetaLowerSegment 3023108352 3023239424 (60460604021753 / 20000)
      (302316189870247 / 100000) := by
  exact
    packedTile65536 3023108352 3023239424 14 6033 54982 31 _ _ (1091477 / 50000) (2182957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3023239424 :
    ThetaLowerSegment 3023239424 3023370496 (302316189870247 / 100000)
      (302329329094449 / 100000) := by
  exact
    packedTile65536 3023239424 3023370496 14 6019 54983 31 _ _ (1091479 / 50000) (2182961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3023370496 :
    ThetaLowerSegment 3023370496 3023501568 (302329329094449 / 100000)
      (302342601503409 / 100000) := by
  exact
    packedTile65536 3023370496 3023501568 14 6080 54985 31 _ _ (1091481 / 50000) (436593 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3023501568 :
    ThetaLowerSegment 3023501568 3023632640 (302342601503409 / 100000)
      (60471152085697 / 20000) := by
  exact
    packedTile65536 3023501568 3023632640 14 6028 54986 31 _ _ (2182967 / 100000) (218297 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3023632640 :
    ThetaLowerSegment 3023632640 3023763712 (60471152085697 / 20000)
      (302368845156659 / 100000) := by
  exact
    packedTile65536 3023632640 3023763712 14 5994 54987 31 _ _ (2182971 / 100000) (1091487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3023763712 :
    ThetaLowerSegment 3023763712 3023894784 (302368845156659 / 100000)
      (302381777100559 / 100000) := by
  exact
    packedTile65536 3023763712 3023894784 14 5924 54988 31 _ _ (87319 / 4000) (1091489 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3023894784 :
    ThetaLowerSegment 3023894784 3024025856 (302381777100559 / 100000)
      (302394826954999 / 100000) := by
  exact
    packedTile65536 3023894784 3024025856 14 5978 54989 31 _ _ (109149 / 5000) (2182983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024025856 :
    ThetaLowerSegment 3024025856 3024156928 (302394826954999 / 100000)
      (302407979433599 / 100000) := by
  exact
    packedTile65536 3024025856 3024156928 14 6025 54991 31 _ _ (272873 / 12500) (2182987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024156928 :
    ThetaLowerSegment 3024156928 3024288000 (302407979433599 / 100000)
      (60484211979539 / 20000) := by
  exact
    packedTile65536 3024156928 3024288000 14 5992 54992 31 _ _ (545747 / 25000) (2182991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024288000 :
    ThetaLowerSegment 3024288000 3024419072 (60484211979539 / 20000)
      (302434166587667 / 100000) := by
  exact
    packedTile65536 3024288000 3024419072 14 6004 54993 31 _ _ (2182993 / 100000) (545749 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024419072 :
    ThetaLowerSegment 3024419072 3024550144 (302434166587667 / 100000)
      (75611792675199 / 25000) := by
  exact
    packedTile65536 3024419072 3024550144 14 5957 54994 31 _ _ (2182997 / 100000) (2183 / 100)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024550144 :
    ThetaLowerSegment 3024550144 3024681216 (75611792675199 / 25000)
      (302460017661681 / 100000) := by
  exact
    packedTile65536 3024550144 3024681216 14 5885 54995 31 _ _ (2183001 / 100000) (545751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024681216 :
    ThetaLowerSegment 3024681216 3024812288 (302460017661681 / 100000)
      (302473272874113 / 100000) := by
  exact
    packedTile65536 3024681216 3024812288 14 6072 54997 31 _ _ (1091503 / 50000) (2183009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024812288 :
    ThetaLowerSegment 3024812288 3024943360 (302473272874113 / 100000)
      (302486357836053 / 100000) := by
  exact
    packedTile65536 3024812288 3024943360 14 5994 54998 31 _ _ (218301 / 10000) (2183013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3024943360 :
    ThetaLowerSegment 3024943360 3025074432 (302486357836053 / 100000)
      (60499888127791 / 20000) := by
  exact
    packedTile65536 3024943360 3025074432 14 5993 54999 31 _ _ (1091507 / 50000) (2183017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025074432 :
    ThetaLowerSegment 3025074432 3025205504 (60499888127791 / 20000) (75628101397199 / 25000) := by
  exact
    packedTile65536 3025074432 3025205504 14 5939 55000 31 _ _ (2183019 / 100000) (1091511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025205504 :
    ThetaLowerSegment 3025205504 3025336576 (75628101397199 / 25000)
      (302525436053083 / 100000) := by
  exact
    packedTile65536 3025205504 3025336576 14 5969 55001 31 _ _ (2183023 / 100000) (1091513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025336576 :
    ThetaLowerSegment 3025336576 3025467648 (302525436053083 / 100000)
      (302538529849029 / 100000) := by
  exact
    packedTile65536 3025336576 3025467648 14 5998 55003 31 _ _ (2183027 / 100000) (218303 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025467648 :
    ThetaLowerSegment 3025467648 3025598720 (302538529849029 / 100000)
      (302551643322253 / 100000) := by
  exact
    packedTile65536 3025467648 3025598720 14 6007 55004 31 _ _ (272879 / 12500) (436607 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025598720 :
    ThetaLowerSegment 3025598720 3025729792 (302551643322253 / 100000)
      (60512942631757 / 20000) := by
  exact
    packedTile65536 3025598720 3025729792 14 5987 55005 31 _ _ (545759 / 25000) (2183039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025729792 :
    ThetaLowerSegment 3025729792 3025860864 (60512942631757 / 20000) (60515543505613 / 20000) := by
  exact
    packedTile65536 3025729792 3025860864 14 5957 55006 31 _ _ (13644 / 625) (2183043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025860864 :
    ThetaLowerSegment 3025860864 3025991936 (60515543505613 / 20000) (60518174511447 / 20000) := by
  exact
    packedTile65536 3025860864 3025991936 14 6026 55007 31 _ _ (436609 / 20000) (272881 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3025991936 :
    ThetaLowerSegment 3025991936 3026123008 (60518174511447 / 20000)
      (302604180423939 / 100000) := by
  exact
    packedTile65536 3025991936 3026123008 14 6096 55009 31 _ _ (2183049 / 100000) (545763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3026123008 :
    ThetaLowerSegment 3026123008 3026254080 (302604180423939 / 100000) (9456790028906 / 3125) := by
  exact
    packedTile65536 3026123008 3026254080 14 6001 55010 31 _ _ (2183053 / 100000) (136441 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3026254080 :
    ThetaLowerSegment 3026254080 3026385152 (9456790028906 / 3125) (75657560980849 / 25000) := by
  exact
    packedTile65536 3026254080 3026385152 14 5938 55011 31 _ _ (1091529 / 50000) (2183061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3026385152 :
    ThetaLowerSegment 3026385152 3026516224 (75657560980849 / 25000) (75660826841601 / 25000) := by
  exact
    packedTile65536 3026385152 3026516224 14 5984 55012 31 _ _ (1091531 / 50000) (436613 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3026516224 :
    ThetaLowerSegment 3026516224 3026647296 (75660826841601 / 25000) (151328245450989 / 50000) := by
  exact
    packedTile65536 3026516224 3026647296 14 6039 55013 31 _ _ (1091533 / 50000) (2183069 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3026647296 :
    ThetaLowerSegment 3026647296 3026778368 (151328245450989 / 50000) (30266948454057 / 10000) := by
  exact
    packedTile65536 3026647296 3026778368 14 5952 55014 31 _ _ (2183071 / 100000) (1091537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3026778368 :
    ThetaLowerSegment 3026778368 3026909440 (30266948454057 / 10000) (30268256552597 / 10000) := by
  exact
    packedTile65536 3026778368 3026909440 14 5992 55016 31 _ _ (87323 / 4000) (1091539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3026909440 :
    ThetaLowerSegment 3026909440 3027040512 (30268256552597 / 10000) (60539126250757 / 20000) := by
  exact
    packedTile65536 3026909440 3027040512 14 5985 55017 31 _ _ (2183079 / 100000) (1091541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027040512 :
    ThetaLowerSegment 3027040512 3027171584 (60539126250757 / 20000)
      (302708731940869 / 100000) := by
  exact
    packedTile65536 3027040512 3027171584 14 6001 55018 31 _ _ (545771 / 25000) (2183087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027171584 :
    ThetaLowerSegment 3027171584 3027302656 (302708731940869 / 100000)
      (302721874130629 / 100000) := by
  exact
    packedTile65536 3027171584 3027302656 14 6020 55019 31 _ _ (136443 / 6250) (2183091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027302656 :
    ThetaLowerSegment 3027302656 3027433728 (302721874130629 / 100000)
      (302734802401453 / 100000) := by
  exact
    packedTile65536 3027302656 3027433728 14 5922 55020 31 _ _ (545773 / 25000) (436619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027433728 :
    ThetaLowerSegment 3027433728 3027564800 (302734802401453 / 100000)
      (151373947217081 / 50000) := by
  exact
    packedTile65536 3027433728 3027564800 14 5997 55022 31 _ _ (2183097 / 100000) (21831 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027564800 :
    ThetaLowerSegment 3027564800 3027695872 (151373947217081 / 50000) (37845114851841 / 12500) := by
  exact
    packedTile65536 3027564800 3027695872 14 5966 55023 31 _ _ (2183101 / 100000) (68222 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027695872 :
    ThetaLowerSegment 3027695872 3027826944 (37845114851841 / 12500) (151387006539259 / 50000) := by
  exact
    packedTile65536 3027695872 3027826944 14 5998 55024 31 _ _ (436621 / 20000) (545777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027826944 :
    ThetaLowerSegment 3027826944 3027958016 (151387006539259 / 50000)
      (151393579883469 / 50000) := by
  exact
    packedTile65536 3027826944 3027958016 14 6022 55025 31 _ _ (218311 / 10000) (2183113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3027958016 :
    ThetaLowerSegment 3027958016 3028089088 (151393579883469 / 50000) (37850041857491 / 12500) := by
  exact
    packedTile65536 3027958016 3028089088 14 6035 55026 31 _ _ (1091557 / 50000) (2183117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028089088 :
    ThetaLowerSegment 3028089088 3028220160 (37850041857491 / 12500) (75703361666659 / 25000) := by
  exact
    packedTile65536 3028089088 3028220160 14 6006 55028 31 _ _ (1091559 / 50000) (2183121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028220160 :
    ThetaLowerSegment 3028220160 3028351232 (75703361666659 / 25000)
      (302826656743909 / 100000) := by
  exact
    packedTile65536 3028220160 3028351232 14 6051 55029 31 _ _ (2183123 / 100000) (1091563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028351232 :
    ThetaLowerSegment 3028351232 3028482304 (302826656743909 / 100000)
      (302839825365973 / 100000) := by
  exact
    packedTile65536 3028351232 3028482304 14 6032 55030 31 _ _ (2183127 / 100000) (218313 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028482304 :
    ThetaLowerSegment 3028482304 3028613376 (302839825365973 / 100000)
      (302852806262899 / 100000) := by
  exact
    packedTile65536 3028482304 3028613376 14 5946 55031 31 _ _ (2183131 / 100000) (1091567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028613376 :
    ThetaLowerSegment 3028613376 3028744448 (302852806262899 / 100000) (12114637600363 / 4000) := by
  exact
    packedTile65536 3028613376 3028744448 14 6016 55032 31 _ _ (68223 / 3125) (2183139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028744448 :
    ThetaLowerSegment 3028744448 3028875520 (12114637600363 / 4000) (12115167230127 / 4000) := by
  exact
    packedTile65536 3028744448 3028875520 14 6065 55034 31 _ _ (109157 / 5000) (2183143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3028875520 :
    ThetaLowerSegment 3028875520 3029006592 (12115167230127 / 4000) (302892336378919 / 100000) := by
  exact
    packedTile65536 3028875520 3029006592 14 6026 55035 31 _ _ (272893 / 12500) (2183147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029006592 :
    ThetaLowerSegment 3029006592 3029137664 (302892336378919 / 100000)
      (30290552041573 / 10000) := by
  exact
    packedTile65536 3029006592 3029137664 14 6039 55036 31 _ _ (2183149 / 100000) (136447 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029137664 :
    ThetaLowerSegment 3029137664 3029268736 (30290552041573 / 10000)
      (302918769971287 / 100000) := by
  exact
    packedTile65536 3029137664 3029268736 14 6069 55037 31 _ _ (2183153 / 100000) (545789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029268736 :
    ThetaLowerSegment 3029268736 3029399808 (302918769971287 / 100000)
      (30293160475129 / 10000) := by
  exact
    packedTile65536 3029268736 3029399808 14 5879 55038 31 _ _ (2183157 / 100000) (54579 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029399808 :
    ThetaLowerSegment 3029399808 3029530880 (30293160475129 / 10000) (9467021923129 / 3125) := by
  exact
    packedTile65536 3029399808 3029530880 14 5999 55039 31 _ _ (1091581 / 50000) (436633 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029530880 :
    ThetaLowerSegment 3029530880 3029661952 (9467021923129 / 3125) (151478868612157 / 50000) := by
  exact
    packedTile65536 3029530880 3029661952 14 5971 55041 31 _ _ (1091583 / 50000) (2183169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029661952 :
    ThetaLowerSegment 3029661952 3029793024 (151478868612157 / 50000) (75742646294941 / 25000) := by
  exact
    packedTile65536 3029661952 3029793024 14 5885 55042 31 _ _ (218317 / 10000) (2183173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029793024 :
    ThetaLowerSegment 3029793024 3029924096 (75742646294941 / 25000)
      (302983782472639 / 100000) := by
  exact
    packedTile65536 3029793024 3029924096 14 6045 55043 31 _ _ (87327 / 4000) (1091589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3029924096 :
    ThetaLowerSegment 3029924096 3030055168 (302983782472639 / 100000) (9468651661416 / 3125) := by
  exact
    packedTile65536 3029924096 3030055168 14 5987 55044 31 _ _ (2183179 / 100000) (1091591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030055168 :
    ThetaLowerSegment 3030055168 3030186240 (9468651661416 / 3125) (303009805990051 / 100000) := by
  exact
    packedTile65536 3030055168 3030186240 14 5933 55045 31 _ _ (2183183 / 100000) (1091593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030186240 :
    ThetaLowerSegment 3030186240 3030317312 (303009805990051 / 100000) (242418283919 / 80) := by
  exact
    packedTile65536 3030186240 3030317312 14 5977 55047 31 _ _ (2183187 / 100000) (218319 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030317312 :
    ThetaLowerSegment 3030317312 3030448384 (242418283919 / 80) (151518008681659 / 50000) := by
  exact
    packedTile65536 3030317312 3030448384 14 6029 55048 31 _ _ (272899 / 12500) (436639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030448384 :
    ThetaLowerSegment 3030448384 3030579456 (151518008681659 / 50000)
      (151524541895689 / 50000) := by
  exact
    packedTile65536 3030448384 3030579456 14 5985 55049 31 _ _ (545799 / 25000) (2183199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030579456 :
    ThetaLowerSegment 3030579456 3030710528 (151524541895689 / 50000)
      (151531063114089 / 50000) := by
  exact
    packedTile65536 3030579456 3030710528 14 5974 55050 31 _ _ (2729 / 125) (2183203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030710528 :
    ThetaLowerSegment 3030710528 3030841600 (151531063114089 / 50000) (18942204593043 / 6250) := by
  exact
    packedTile65536 3030710528 3030841600 14 6022 55051 31 _ _ (436641 / 20000) (272901 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030841600 :
    ThetaLowerSegment 3030841600 3030972672 (18942204593043 / 6250) (12123538664827 / 4000) := by
  exact
    packedTile65536 3030841600 3030972672 14 6043 55053 31 _ _ (2183209 / 100000) (545803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3030972672 :
    ThetaLowerSegment 3030972672 3031103744 (12123538664827 / 4000) (151550794957009 / 50000) := by
  exact
    packedTile65536 3030972672 3031103744 14 6011 55054 31 _ _ (2183213 / 100000) (136451 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3031103744 :
    ThetaLowerSegment 3031103744 3031234816 (151550794957009 / 50000)
      (151557442855819 / 50000) := by
  exact
    packedTile65536 3031103744 3031234816 14 6090 55055 31 _ _ (1091609 / 50000) (2183221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3031234816 :
    ThetaLowerSegment 3031234816 3031365888 (151557442855819 / 50000) (15156403727787 / 5000) := by
  exact
    packedTile65536 3031234816 3031365888 14 6041 55056 31 _ _ (1091611 / 50000) (87329 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3031365888 :
    ThetaLowerSegment 3031365888 3031496960 (15156403727787 / 5000) (7578528801987 / 2500) := by
  exact
    packedTile65536 3031365888 3031496960 14 5990 55057 31 _ _ (1091613 / 50000) (2183229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3031496960 :
    ThetaLowerSegment 3031496960 3031628032 (7578528801987 / 2500) (303154275481021 / 100000) := by
  exact
    packedTile65536 3031496960 3031628032 14 6011 55059 31 _ _ (2183231 / 100000) (1091617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3031628032 :
    ThetaLowerSegment 3031628032 3031759104 (303154275481021 / 100000)
      (303167575748641 / 100000) := by
  exact
    packedTile65536 3031628032 3031759104 14 6092 55060 31 _ _ (436647 / 20000) (1091619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3031759104 :
    ThetaLowerSegment 3031759104 3031890176 (303167575748641 / 100000)
      (303180614051949 / 100000) := by
  exact
    packedTile65536 3031759104 3031890176 14 5972 55061 31 _ _ (2183239 / 100000) (1091621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3031890176 :
    ThetaLowerSegment 3031890176 3032021248 (303180614051949 / 100000)
      (303193866343029 / 100000) := by
  exact
    packedTile65536 3031890176 3032021248 14 6070 55062 31 _ _ (545811 / 25000) (2183247 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032021248 :
    ThetaLowerSegment 3032021248 3032152320 (303193866343029 / 100000)
      (303207026961973 / 100000) := by
  exact
    packedTile65536 3032021248 3032152320 14 6028 55063 31 _ _ (136453 / 6250) (2183251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032152320 :
    ThetaLowerSegment 3032152320 3032283392 (303207026961973 / 100000)
      (303220220353809 / 100000) := by
  exact
    packedTile65536 3032152320 3032283392 14 6043 55064 31 _ _ (545813 / 25000) (436651 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032283392 :
    ThetaLowerSegment 3032283392 3032414464 (303220220353809 / 100000)
      (75808292312769 / 25000) := by
  exact
    packedTile65536 3032283392 3032414464 14 5931 55066 31 _ _ (2183257 / 100000) (109163 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032414464 :
    ThetaLowerSegment 3032414464 3032545536 (75808292312769 / 25000) (9476445627626 / 3125) := by
  exact
    packedTile65536 3032414464 3032545536 14 5996 55067 31 _ _ (2183261 / 100000) (68227 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032545536 :
    ThetaLowerSegment 3032545536 3032676608 (9476445627626 / 3125) (303259291992817 / 100000) := by
  exact
    packedTile65536 3032545536 3032676608 14 5969 55068 31 _ _ (436653 / 20000) (545817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032676608 :
    ThetaLowerSegment 3032676608 3032807680 (303259291992817 / 100000)
      (303272507326127 / 100000) := by
  exact
    packedTile65536 3032676608 3032807680 14 6053 55069 31 _ _ (218327 / 10000) (2183273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032807680 :
    ThetaLowerSegment 3032807680 3032938752 (303272507326127 / 100000)
      (303285646269059 / 100000) := by
  exact
    packedTile65536 3032807680 3032938752 14 6018 55070 31 _ _ (1091637 / 50000) (2183277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3032938752 :
    ThetaLowerSegment 3032938752 3033069824 (303285646269059 / 100000)
      (303298890033407 / 100000) := by
  exact
    packedTile65536 3032938752 3033069824 14 6066 55072 31 _ _ (1091639 / 50000) (2183281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033069824 :
    ThetaLowerSegment 3033069824 3033200896 (303298890033407 / 100000) (1895700085922 / 625) := by
  exact
    packedTile65536 3033069824 3033200896 14 6011 55073 31 _ _ (2183283 / 100000) (1091643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033200896 :
    ThetaLowerSegment 3033200896 3033331968 (1895700085922 / 625) (303325045787623 / 100000) := by
  exact
    packedTile65536 3033200896 3033331968 14 5969 55074 31 _ _ (2183287 / 100000) (218329 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033331968 :
    ThetaLowerSegment 3033331968 3033463040 (303325045787623 / 100000)
      (303338036369073 / 100000) := by
  exact
    packedTile65536 3033331968 3033463040 14 5950 55075 31 _ _ (2183291 / 100000) (1091647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033463040 :
    ThetaLowerSegment 3033463040 3033594112 (303338036369073 / 100000)
      (303351079379377 / 100000) := by
  exact
    packedTile65536 3033463040 3033594112 14 5974 55076 31 _ _ (68228 / 3125) (2183299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033594112 :
    ThetaLowerSegment 3033594112 3033725184 (303351079379377 / 100000)
      (303364176996077 / 100000) := by
  exact
    packedTile65536 3033594112 3033725184 14 5999 55078 31 _ _ (21833 / 1000) (2183303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033725184 :
    ThetaLowerSegment 3033725184 3033856256 (303364176996077 / 100000)
      (303377534449949 / 100000) := by
  exact
    packedTile65536 3033725184 3033856256 14 6118 55079 31 _ _ (272913 / 12500) (2183307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033856256 :
    ThetaLowerSegment 3033856256 3033987328 (303377534449949 / 100000)
      (151695322610247 / 50000) := by
  exact
    packedTile65536 3033856256 3033987328 14 6005 55080 31 _ _ (2183309 / 100000) (136457 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3033987328 :
    ThetaLowerSegment 3033987328 3034118400 (151695322610247 / 50000)
      (151701959881767 / 50000) := by
  exact
    packedTile65536 3033987328 3034118400 14 6080 55081 31 _ _ (2183313 / 100000) (545829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3034118400 :
    ThetaLowerSegment 3034118400 3034249472 (151701959881767 / 50000)
      (303417165947773 / 100000) := by
  exact
    packedTile65536 3034118400 3034249472 14 6067 55082 31 _ _ (2183317 / 100000) (54583 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3034249472 :
    ThetaLowerSegment 3034249472 3034380544 (303417165947773 / 100000) (15171505324567 / 5000) := by
  exact
    packedTile65536 3034249472 3034380544 14 5927 55084 31 _ _ (2183321 / 100000) (545831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3034380544 :
    ThetaLowerSegment 3034380544 3034511616 (15171505324567 / 5000) (151721604315333 / 50000) := by
  exact
    packedTile65536 3034380544 3034511616 14 6001 55085 31 _ _ (1091663 / 50000) (2183329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3034511616 :
    ThetaLowerSegment 3034511616 3034642688 (151721604315333 / 50000) (9483007119608 / 3125) := by
  exact
    packedTile65536 3034511616 3034642688 14 5963 55086 31 _ _ (218333 / 10000) (2183333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3034642688 :
    ThetaLowerSegment 3034642688 3034773760 (9483007119608 / 3125) (151734634440719 / 50000) := by
  exact
    packedTile65536 3034642688 3034773760 14 5973 55087 31 _ _ (1091667 / 50000) (2183337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3034773760 :
    ThetaLowerSegment 3034773760 3034904832 (151734634440719 / 50000)
      (151741245591211 / 50000) := by
  exact
    packedTile65536 3034773760 3034904832 14 6056 55088 31 _ _ (2183339 / 100000) (1091671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3034904832 :
    ThetaLowerSegment 3034904832 3035035904 (151741245591211 / 50000) (30349562617391 / 10000) := by
  exact
    packedTile65536 3034904832 3035035904 14 6016 55089 31 _ _ (2183343 / 100000) (1091673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035035904 :
    ThetaLowerSegment 3035035904 3035166976 (30349562617391 / 10000)
      (303508658572153 / 100000) := by
  exact
    packedTile65536 3035035904 3035166976 14 5969 55091 31 _ _ (2183347 / 100000) (43667 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035166976 :
    ThetaLowerSegment 3035166976 3035298048 (303508658572153 / 100000)
      (303521732483929 / 100000) := by
  exact
    packedTile65536 3035166976 3035298048 14 5988 55092 31 _ _ (272919 / 12500) (436671 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035298048 :
    ThetaLowerSegment 3035298048 3035429120 (303521732483929 / 100000)
      (303534919954169 / 100000) := by
  exact
    packedTile65536 3035298048 3035429120 14 6040 55093 31 _ _ (545839 / 25000) (2183359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035429120 :
    ThetaLowerSegment 3035429120 3035560192 (303534919954169 / 100000)
      (303548007014009 / 100000) := by
  exact
    packedTile65536 3035429120 3035560192 14 5994 55094 31 _ _ (13646 / 625) (2183363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035560192 :
    ThetaLowerSegment 3035560192 3035691264 (303548007014009 / 100000)
      (37945126119073 / 12500) := by
  exact
    packedTile65536 3035560192 3035691264 14 5955 55095 31 _ _ (436673 / 20000) (272921 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035691264 :
    ThetaLowerSegment 3035691264 3035822336 (37945126119073 / 12500)
      (303574115716691 / 100000) := by
  exact
    packedTile65536 3035691264 3035822336 14 6003 55097 31 _ _ (2183369 / 100000) (545843 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035822336 :
    ThetaLowerSegment 3035822336 3035953408 (303574115716691 / 100000)
      (75896780517413 / 25000) := by
  exact
    packedTile65536 3035822336 3035953408 14 5957 55098 31 _ _ (2183373 / 100000) (136461 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3035953408 :
    ThetaLowerSegment 3035953408 3036084480 (75896780517413 / 25000) (3036002572717 / 1000) := by
  exact
    packedTile65536 3035953408 3036084480 14 6016 55099 31 _ _ (1091689 / 50000) (2183381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036084480 :
    ThetaLowerSegment 3036084480 3036215552 (3036002572717 / 1000) (151806682056923 / 50000) := by
  exact
    packedTile65536 3036084480 3036215552 14 6003 55100 31 _ _ (1091691 / 50000) (436677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036215552 :
    ThetaLowerSegment 3036215552 3036346624 (151806682056923 / 50000)
      (151813157979799 / 50000) := by
  exact
    packedTile65536 3036215552 3036346624 14 5932 55101 31 _ _ (1091693 / 50000) (2183389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036346624 :
    ThetaLowerSegment 3036346624 3036477696 (151813157979799 / 50000) (75909828967403 / 25000) := by
  exact
    packedTile65536 3036346624 3036477696 14 5954 55103 31 _ _ (2183391 / 100000) (1091697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036477696 :
    ThetaLowerSegment 3036477696 3036608768 (75909828967403 / 25000) (75913143361013 / 25000) := by
  exact
    packedTile65536 3036477696 3036608768 14 6072 55104 31 _ _ (436679 / 20000) (1091699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036608768 :
    ThetaLowerSegment 3036608768 3036739840 (75913143361013 / 25000)
      (303665676021451 / 100000) := by
  exact
    packedTile65536 3036608768 3036739840 14 6001 55105 31 _ _ (2183399 / 100000) (1091701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036739840 :
    ThetaLowerSegment 3036739840 3036870912 (303665676021451 / 100000)
      (303678970768407 / 100000) := by
  exact
    packedTile65536 3036739840 3036870912 14 6089 55106 31 _ _ (545851 / 25000) (2183407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3036870912 :
    ThetaLowerSegment 3036870912 3037001984 (303678970768407 / 100000)
      (303692197854071 / 100000) := by
  exact
    packedTile65536 3036870912 3037001984 14 6058 55107 31 _ _ (136463 / 6250) (2183411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037001984 :
    ThetaLowerSegment 3037001984 3037133056 (303692197854071 / 100000)
      (303705287409011 / 100000) := by
  exact
    packedTile65536 3037001984 3037133056 14 5995 55109 32 _ _ (545853 / 25000) (436683 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037133056 :
    ThetaLowerSegment 3037133056 3037264128 (303705287409011 / 100000)
      (60743666227239 / 20000) := by
  exact
    packedTile65536 3037133056 3037264128 14 5974 55110 32 _ _ (272927 / 12500) (2183419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037264128 :
    ThetaLowerSegment 3037264128 3037395200 (60743666227239 / 20000) (75932869378509 / 25000) := by
  exact
    packedTile65536 3037264128 3037395200 14 6021 55111 32 _ _ (2183421 / 100000) (68232 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037395200 :
    ThetaLowerSegment 3037395200 3037526272 (75932869378509 / 25000)
      (303744623915961 / 100000) := by
  exact
    packedTile65536 3037395200 3037526272 14 6021 55112 32 _ _ (87337 / 4000) (545857 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037526272 :
    ThetaLowerSegment 3037526272 3037657344 (303744623915961 / 100000)
      (151878893904701 / 50000) := by
  exact
    packedTile65536 3037526272 3037657344 14 6029 55113 32 _ _ (2183429 / 100000) (272929 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037657344 :
    ThetaLowerSegment 3037657344 3037788416 (151878893904701 / 50000)
      (151885393987719 / 50000) := by
  exact
    packedTile65536 3037657344 3037788416 14 5954 55114 32 _ _ (1091717 / 50000) (2183437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037788416 :
    ThetaLowerSegment 3037788416 3037919488 (151885393987719 / 50000)
      (151891996704231 / 50000) := by
  exact
    packedTile65536 3037788416 3037919488 14 6048 55116 32 _ _ (1091719 / 50000) (2183441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3037919488 :
    ThetaLowerSegment 3037919488 3038050560 (151891996704231 / 50000) (75949270785813 / 25000) := by
  exact
    packedTile65536 3037919488 3038050560 14 5995 55117 32 _ _ (1091721 / 50000) (436689 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038050560 :
    ThetaLowerSegment 3038050560 3038181632 (75949270785813 / 25000)
      (303810111771501 / 100000) := by
  exact
    packedTile65536 3038050560 3038181632 14 5967 55118 32 _ _ (2183447 / 100000) (43669 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038181632 :
    ThetaLowerSegment 3038181632 3038312704 (303810111771501 / 100000)
      (30382312295601 / 10000) := by
  exact
    packedTile65536 3038181632 3038312704 14 5959 55119 32 _ _ (2183451 / 100000) (1091727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038312704 :
    ThetaLowerSegment 3038312704 3038443776 (30382312295601 / 10000) (30383634595949 / 10000) := by
  exact
    packedTile65536 3038312704 3038443776 14 6056 55120 32 _ _ (436691 / 20000) (1091729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038443776 :
    ThetaLowerSegment 3038443776 3038574848 (30383634595949 / 10000) (30384957554363 / 10000) := by
  exact
    packedTile65536 3038443776 3038574848 14 6059 55122 32 _ _ (109173 / 5000) (2183463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038574848 :
    ThetaLowerSegment 3038574848 3038705920 (30384957554363 / 10000) (151931296677999 / 50000) := by
  exact
    packedTile65536 3038574848 3038705920 14 5962 55123 32 _ _ (272933 / 12500) (2183467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038705920 :
    ThetaLowerSegment 3038705920 3038836992 (151931296677999 / 50000)
      (151937806687841 / 50000) := by
  exact
    packedTile65536 3038705920 3038836992 14 5963 55124 32 _ _ (545867 / 25000) (2183471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038836992 :
    ThetaLowerSegment 3038836992 3038968064 (151937806687841 / 50000) (60777712710809 / 20000) := by
  exact
    packedTile65536 3038836992 3038968064 14 5931 55125 32 _ _ (2183473 / 100000) (545869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3038968064 :
    ThetaLowerSegment 3038968064 3039099136 (60777712710809 / 20000)
      (303901655682137 / 100000) := by
  exact
    packedTile65536 3038968064 3039099136 14 5996 55126 32 _ _ (2183477 / 100000) (54587 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3039099136 :
    ThetaLowerSegment 3039099136 3039230208 (303901655682137 / 100000)
      (303914848274339 / 100000) := by
  exact
    packedTile65536 3039099136 3039230208 14 6042 55128 32 _ _ (2183481 / 100000) (545871 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3039230208 :
    ThetaLowerSegment 3039230208 3039361280 (303914848274339 / 100000) (486284896877 / 160) := by
  exact
    packedTile65536 3039230208 3039361280 14 6051 55129 32 _ _ (1091743 / 50000) (2183489 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3039361280 :
    ThetaLowerSegment 3039361280 3039492352 (486284896877 / 160) (60788206969141 / 20000) := by
  exact
    packedTile65536 3039361280 3039492352 14 5942 55130 32 _ _ (218349 / 10000) (2183493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3039492352 :
    ThetaLowerSegment 3039492352 3039623424 (60788206969141 / 20000)
      (303954079038861 / 100000) := by
  exact
    packedTile65536 3039492352 3039623424 14 5974 55131 32 _ _ (1091747 / 50000) (2183497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3039623424 :
    ThetaLowerSegment 3039623424 3039754496 (303954079038861 / 100000)
      (303967369991187 / 100000) := by
  exact
    packedTile65536 3039623424 3039754496 14 6087 55132 32 _ _ (1091749 / 50000) (2183501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3039754496 :
    ThetaLowerSegment 3039754496 3039885568 (303967369991187 / 100000)
      (75995099738397 / 25000) := by
  exact
    packedTile65536 3039754496 3039885568 14 5967 55133 32 _ _ (2183503 / 100000) (1091753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3039885568 :
    ThetaLowerSegment 3039885568 3040016640 (75995099738397 / 25000) (151996878824707 / 50000) := by
  exact
    packedTile65536 3039885568 3040016640 14 6118 55135 32 _ _ (2183507 / 100000) (218351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040016640 :
    ThetaLowerSegment 3040016640 3040147712 (151996878824707 / 50000) (76001698302521 / 25000) := by
  exact
    packedTile65536 3040016640 3040147712 14 5970 55136 32 _ _ (2183511 / 100000) (1091757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040147712 :
    ThetaLowerSegment 3040147712 3040278784 (76001698302521 / 25000) (9500617944147 / 3125) := by
  exact
    packedTile65536 3040147712 3040278784 14 5945 55137 32 _ _ (545879 / 25000) (2183519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040278784 :
    ThetaLowerSegment 3040278784 3040409856 (9500617944147 / 3125) (9501030492957 / 3125) := by
  exact
    packedTile65536 3040278784 3040409856 14 6046 55138 32 _ _ (13647 / 625) (2183523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040409856 :
    ThetaLowerSegment 3040409856 3040540928 (9501030492957 / 3125) (15202296094421 / 5000) := by
  exact
    packedTile65536 3040409856 3040540928 14 5929 55139 32 _ _ (545881 / 25000) (2183527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040540928 :
    ThetaLowerSegment 3040540928 3040672000 (15202296094421 / 5000) (152029640359421 / 50000) := by
  exact
    packedTile65536 3040540928 3040672000 14 6118 55141 32 _ _ (2183529 / 100000) (545883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040672000 :
    ThetaLowerSegment 3040672000 3040803072 (152029640359421 / 50000)
      (304072510745289 / 100000) := by
  exact
    packedTile65536 3040672000 3040803072 14 6059 55142 32 _ _ (2183533 / 100000) (136471 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040803072 :
    ThetaLowerSegment 3040803072 3040934144 (304072510745289 / 100000)
      (152042759037599 / 50000) := by
  exact
    packedTile65536 3040803072 3040934144 14 5957 55143 32 _ _ (2183537 / 100000) (109177 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3040934144 :
    ThetaLowerSegment 3040934144 3041065216 (152042759037599 / 50000)
      (152049309663599 / 50000) := by
  exact
    packedTile65536 3040934144 3041065216 14 6000 55144 32 _ _ (1091771 / 50000) (436709 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041065216 :
    ThetaLowerSegment 3041065216 3041196288 (152049309663599 / 50000) (76027938339097 / 25000) := by
  exact
    packedTile65536 3041065216 3041196288 14 6015 55145 32 _ _ (1091773 / 50000) (2183549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041196288 :
    ThetaLowerSegment 3041196288 3041327360 (76027938339097 / 25000) (152062450255469 / 50000) := by
  exact
    packedTile65536 3041196288 3041327360 14 6021 55147 32 _ _ (43671 / 2000) (2183553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041327360 :
    ThetaLowerSegment 3041327360 3041458432 (152062450255469 / 50000)
      (152069035854333 / 50000) := by
  exact
    packedTile65536 3041327360 3041458432 14 6032 55148 32 _ _ (1091777 / 50000) (2183557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041458432 :
    ThetaLowerSegment 3041458432 3041589504 (152069035854333 / 50000)
      (304151223284523 / 100000) := by
  exact
    packedTile65536 3041458432 3041589504 14 6023 55149 32 _ _ (2183559 / 100000) (1091781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041589504 :
    ThetaLowerSegment 3041589504 3041720576 (304151223284523 / 100000)
      (304164294092641 / 100000) := by
  exact
    packedTile65536 3041589504 3041720576 14 5986 55150 32 _ _ (2183563 / 100000) (1091783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041720576 :
    ThetaLowerSegment 3041720576 3041851648 (304164294092641 / 100000)
      (60835510542293 / 20000) := by
  exact
    packedTile65536 3041720576 3041851648 14 6072 55151 32 _ _ (2183567 / 100000) (218357 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041851648 :
    ThetaLowerSegment 3041851648 3041982720 (60835510542293 / 20000)
      (304190564617013 / 100000) := by
  exact
    packedTile65536 3041851648 3041982720 14 5959 55152 32 _ _ (545893 / 25000) (87343 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3041982720 :
    ThetaLowerSegment 3041982720 3042113792 (304190564617013 / 100000)
      (60840712252273 / 20000) := by
  exact
    packedTile65536 3041982720 3042113792 14 5952 55154 32 _ _ (272947 / 12500) (2183579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3042113792 :
    ThetaLowerSegment 3042113792 3042244864 (60840712252273 / 20000) (60843326434249 / 20000) := by
  exact
    packedTile65536 3042113792 3042244864 14 5986 55155 32 _ _ (109179 / 5000) (2183583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3042244864 :
    ThetaLowerSegment 3042244864 3042375936 (60843326434249 / 20000) (6084593494489 / 2000) := by
  exact
    packedTile65536 3042244864 3042375936 14 5973 55156 32 _ _ (436717 / 20000) (545897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3042375936 :
    ThetaLowerSegment 3042375936 3042507008 (6084593494489 / 2000) (38030350853587 / 12500) := by
  exact
    packedTile65536 3042375936 3042507008 14 6014 55157 32 _ _ (2183589 / 100000) (272949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3042507008 :
    ThetaLowerSegment 3042507008 3042638080 (38030350853587 / 12500)
      (304255932406219 / 100000) := by
  exact
    packedTile65536 3042507008 3042638080 14 6011 55158 32 _ _ (2183593 / 100000) (545899 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3042638080 :
    ThetaLowerSegment 3042638080 3042769152 (304255932406219 / 100000)
      (304268990322259 / 100000) := by
  exact
    packedTile65536 3042638080 3042769152 14 5980 55160 32 _ _ (1091799 / 50000) (2183601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3042769152 :
    ThetaLowerSegment 3042769152 3042900224 (304268990322259 / 100000)
      (304282465330201 / 100000) := by
  exact
    packedTile65536 3042769152 3042900224 14 6171 55161 32 _ _ (1091801 / 50000) (436721 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3042900224 :
    ThetaLowerSegment 3042900224 3043031296 (304282465330201 / 100000)
      (60859123874549 / 20000) := by
  exact
    packedTile65536 3042900224 3043031296 14 6024 55162 32 _ _ (1091803 / 50000) (2183609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043031296 :
    ThetaLowerSegment 3043031296 3043162368 (60859123874549 / 20000) (60861729794723 / 20000) := by
  exact
    packedTile65536 3043031296 3043162368 14 5967 55163 32 _ _ (218361 / 10000) (2183613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043162368 :
    ThetaLowerSegment 3043162368 3043293440 (60861729794723 / 20000) (60864377209549 / 20000) := by
  exact
    packedTile65536 3043162368 3043293440 14 6062 55164 32 _ _ (436723 / 20000) (1091809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043293440 :
    ThetaLowerSegment 3043293440 3043424512 (60864377209549 / 20000) (152167427280493 / 50000) := by
  exact
    packedTile65536 3043293440 3043424512 14 5939 55166 32 _ _ (2183619 / 100000) (1091811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043424512 :
    ThetaLowerSegment 3043424512 3043555584 (152167427280493 / 50000)
      (304347927911887 / 100000) := by
  exact
    packedTile65536 3043424512 3043555584 14 5987 55167 32 _ _ (2183623 / 100000) (1091813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043555584 :
    ThetaLowerSegment 3043555584 3043686656 (304347927911887 / 100000)
      (60872221658099 / 20000) := by
  exact
    packedTile65536 3043555584 3043686656 14 6036 55168 32 _ _ (545907 / 25000) (2183631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043686656 :
    ThetaLowerSegment 3043686656 3043817728 (60872221658099 / 20000)
      (304374048493727 / 100000) := by
  exact
    packedTile65536 3043686656 3043817728 14 5926 55169 32 _ _ (136477 / 6250) (436727 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043817728 :
    ThetaLowerSegment 3043817728 3043948800 (304374048493727 / 100000)
      (60877457575759 / 20000) := by
  exact
    packedTile65536 3043817728 3043948800 14 6063 55170 32 _ _ (545909 / 25000) (2183639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3043948800 :
    ThetaLowerSegment 3043948800 3044079872 (60877457575759 / 20000)
      (304400450866743 / 100000) := by
  exact
    packedTile65536 3043948800 3044079872 14 6028 55171 32 _ _ (2183641 / 100000) (545911 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044079872 :
    ThetaLowerSegment 3044079872 3044210944 (304400450866743 / 100000)
      (304413696857313 / 100000) := by
  exact
    packedTile65536 3044079872 3044210944 14 6066 55173 32 _ _ (436729 / 20000) (68239 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044210944 :
    ThetaLowerSegment 3044210944 3044342016 (304413696857313 / 100000) (9513334117266 / 3125) := by
  exact
    packedTile65536 3044210944 3044342016 14 5951 55174 32 _ _ (2183649 / 100000) (545913 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044342016 :
    ThetaLowerSegment 3044342016 3044473088 (9513334117266 / 3125) (152219939419509 / 50000) := by
  exact
    packedTile65536 3044342016 3044473088 14 6039 55175 32 _ _ (1091827 / 50000) (2183657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044473088 :
    ThetaLowerSegment 3044473088 3044604160 (152219939419509 / 50000)
      (152226499128141 / 50000) := by
  exact
    packedTile65536 3044473088 3044604160 14 6008 55176 32 _ _ (1091829 / 50000) (2183661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044604160 :
    ThetaLowerSegment 3044604160 3044735232 (152226499128141 / 50000) (30446606528969 / 10000) := by
  exact
    packedTile65536 3044604160 3044735232 14 5984 55177 32 _ _ (1091831 / 50000) (436733 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044735232 :
    ThetaLowerSegment 3044735232 3044866304 (30446606528969 / 10000) (152239574908181 / 50000) := by
  exact
    packedTile65536 3044735232 3044866304 14 5992 55179 32 _ _ (1091833 / 50000) (2183669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044866304 :
    ThetaLowerSegment 3044866304 3044997376 (152239574908181 / 50000) (38061527658871 / 12500) := by
  exact
    packedTile65536 3044866304 3044997376 14 5986 55180 32 _ _ (2183671 / 100000) (1091837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3044997376 :
    ThetaLowerSegment 3044997376 3045128448 (38061527658871 / 12500)
      (304505399749593 / 100000) := by
  exact
    packedTile65536 3044997376 3045128448 14 6035 55181 32 _ _ (87347 / 4000) (1091839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3045128448 :
    ThetaLowerSegment 3045128448 3045259520 (304505399749593 / 100000)
      (30451842102747 / 10000) := by
  exact
    packedTile65536 3045128448 3045259520 14 5963 55182 32 _ _ (2183679 / 100000) (1091841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3045259520 :
    ThetaLowerSegment 3045259520 3045390592 (30451842102747 / 10000) (152265740820737 / 50000) := by
  exact
    packedTile65536 3045259520 3045390592 14 5981 55183 32 _ _ (545921 / 25000) (2183687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3045390592 :
    ThetaLowerSegment 3045390592 3045521664 (152265740820737 / 50000)
      (152272344293249 / 50000) := by
  exact
    packedTile65536 3045390592 3045521664 14 6048 55185 32 _ _ (272961 / 12500) (2183691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3045521664 :
    ThetaLowerSegment 3045521664 3045652736 (152272344293249 / 50000)
      (152278925940937 / 50000) := by
  exact
    packedTile65536 3045521664 3045652736 14 6028 55186 32 _ _ (545923 / 25000) (436739 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3045652736 :
    ThetaLowerSegment 3045652736 3045783808 (152278925940937 / 50000) (60914209592569 / 20000) := by
  exact
    packedTile65536 3045652736 3045783808 14 6043 55187 32 _ _ (2183697 / 100000) (21837 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3045783808 :
    ThetaLowerSegment 3045783808 3045914880 (60914209592569 / 20000)
      (304584123964433 / 100000) := by
  exact
    packedTile65536 3045783808 3045914880 14 5988 55188 32 _ _ (2183701 / 100000) (272963 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3045914880 :
    ThetaLowerSegment 3045914880 3046045952 (304584123964433 / 100000)
      (304597121376593 / 100000) := by
  exact
    packedTile65536 3045914880 3046045952 14 5952 55189 32 _ _ (436741 / 20000) (545927 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046045952 :
    ThetaLowerSegment 3046045952 3046177024 (304597121376593 / 100000)
      (304610304433863 / 100000) := by
  exact
    packedTile65536 3046045952 3046177024 14 6037 55190 32 _ _ (218371 / 10000) (2183713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046177024 :
    ThetaLowerSegment 3046177024 3046308096 (304610304433863 / 100000)
      (304623356492441 / 100000) := by
  exact
    packedTile65536 3046177024 3046308096 14 5977 55192 32 _ _ (1091857 / 50000) (2183717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046308096 :
    ThetaLowerSegment 3046308096 3046439168 (304623356492441 / 100000)
      (304636417309799 / 100000) := by
  exact
    packedTile65536 3046308096 3046439168 14 5981 55193 32 _ _ (1091859 / 50000) (2183721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046439168 :
    ThetaLowerSegment 3046439168 3046570240 (304636417309799 / 100000)
      (304649550213907 / 100000) := by
  exact
    packedTile65536 3046439168 3046570240 14 6014 55194 32 _ _ (1091861 / 50000) (87349 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046570240 :
    ThetaLowerSegment 3046570240 3046701312 (304649550213907 / 100000)
      (304662691882993 / 100000) := by
  exact
    packedTile65536 3046570240 3046701312 14 6018 55195 32 _ _ (2183727 / 100000) (218373 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046701312 :
    ThetaLowerSegment 3046701312 3046832384 (304662691882993 / 100000)
      (38084469097263 / 12500) := by
  exact
    packedTile65536 3046701312 3046832384 14 5981 55196 32 _ _ (2183731 / 100000) (1091867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046832384 :
    ThetaLowerSegment 3046832384 3046963456 (38084469097263 / 12500)
      (304688778757379 / 100000) := by
  exact
    packedTile65536 3046832384 3046963456 14 5965 55198 32 _ _ (436747 / 20000) (1091869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3046963456 :
    ThetaLowerSegment 3046963456 3047094528 (304688778757379 / 100000)
      (304702060264059 / 100000) := by
  exact
    packedTile65536 3046963456 3047094528 14 6082 55199 32 _ _ (109187 / 5000) (2183743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3047094528 :
    ThetaLowerSegment 3047094528 3047225600 (304702060264059 / 100000)
      (304715158360571 / 100000) := by
  exact
    packedTile65536 3047094528 3047225600 14 5998 55200 32 _ _ (68242 / 3125) (2183747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3047225600 :
    ThetaLowerSegment 3047225600 3047356672 (304715158360571 / 100000)
      (304728411527183 / 100000) := by
  exact
    packedTile65536 3047225600 3047356672 14 6069 55201 32 _ _ (545937 / 25000) (2183751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3047356672 :
    ThetaLowerSegment 3047356672 3047487744 (304728411527183 / 100000) (243793104669 / 80) := by
  exact
    packedTile65536 3047356672 3047487744 14 5939 55202 32 _ _ (2183753 / 100000) (545939 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3047487744 :
    ThetaLowerSegment 3047487744 3047618816 (243793104669 / 80) (304754420049297 / 100000) := by
  exact
    packedTile65536 3047487744 3047618816 14 5971 55204 32 _ _ (2183757 / 100000) (27297 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3047618816 :
    ThetaLowerSegment 3047618816 3047749888 (304754420049297 / 100000)
      (304767509512731 / 100000) := by
  exact
    packedTile65536 3047618816 3047749888 14 5994 55205 32 _ _ (2183761 / 100000) (545941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3047749888 :
    ThetaLowerSegment 3047749888 3047880960 (304767509512731 / 100000)
      (152390226343943 / 50000) := by
  exact
    packedTile65536 3047749888 3047880960 14 5927 55206 32 _ _ (436753 / 20000) (272971 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3047880960 :
    ThetaLowerSegment 3047880960 3048012032 (152390226343943 / 50000)
      (152396880291133 / 50000) := by
  exact
    packedTile65536 3047880960 3048012032 14 6094 55207 32 _ _ (218377 / 10000) (2183773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048012032 :
    ThetaLowerSegment 3048012032 3048143104 (152396880291133 / 50000) (30480694184213 / 10000) := by
  exact
    packedTile65536 3048012032 3048143104 14 6036 55208 32 _ _ (1091887 / 50000) (2183777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048143104 :
    ThetaLowerSegment 3048143104 3048274176 (30480694184213 / 10000) (152409961109281 / 50000) := by
  exact
    packedTile65536 3048143104 3048274176 14 5944 55209 32 _ _ (1091889 / 50000) (2183781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048274176 :
    ThetaLowerSegment 3048274176 3048405248 (152409961109281 / 50000)
      (152416372696169 / 50000) := by
  exact
    packedTile65536 3048274176 3048405248 14 5872 55211 32 _ _ (2183783 / 100000) (1091893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048405248 :
    ThetaLowerSegment 3048405248 3048536320 (152416372696169 / 50000)
      (152422980835631 / 50000) := by
  exact
    packedTile65536 3048405248 3048536320 14 6052 55212 32 _ _ (2183787 / 100000) (218379 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048536320 :
    ThetaLowerSegment 3048536320 3048667392 (152422980835631 / 50000)
      (304859014190069 / 100000) := by
  exact
    packedTile65536 3048536320 3048667392 14 5977 55213 32 _ _ (2183791 / 100000) (1091897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048667392 :
    ThetaLowerSegment 3048667392 3048798464 (304859014190069 / 100000)
      (304872103863293 / 100000) := by
  exact
    packedTile65536 3048667392 3048798464 14 5994 55214 32 _ _ (545949 / 25000) (2183799 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048798464 :
    ThetaLowerSegment 3048798464 3048929536 (304872103863293 / 100000)
      (304885217582293 / 100000) := by
  exact
    packedTile65536 3048798464 3048929536 14 6005 55215 32 _ _ (10919 / 500) (2183803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3048929536 :
    ThetaLowerSegment 3048929536 3049060608 (304885217582293 / 100000)
      (304898346611941 / 100000) := by
  exact
    packedTile65536 3048929536 3049060608 14 6012 55217 32 _ _ (545951 / 25000) (2183807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049060608 :
    ThetaLowerSegment 3049060608 3049191680 (304898346611941 / 100000)
      (304911421070437 / 100000) := by
  exact
    packedTile65536 3049060608 3049191680 14 5987 55218 32 _ _ (68244 / 3125) (2183811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049191680 :
    ThetaLowerSegment 3049191680 3049322752 (304911421070437 / 100000)
      (38115602345399 / 12500) := by
  exact
    packedTile65536 3049191680 3049322752 14 6135 55219 32 _ _ (2183813 / 100000) (272977 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049322752 :
    ThetaLowerSegment 3049322752 3049339136 (38115602345399 / 12500)
      (304926428236321 / 100000) := by
  exact
    packedTile65536 3049322752 3049339136 11 737 55220 32 _ _ (2183817 / 100000) (109191 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3049339136 :
    ThetaLowerSegment 3049339136 3049341184 (304926428236321 / 100000)
      (304926605125579 / 100000) := by
  exact
    packedTile65536 3049339136 3049341184 8 81 55220 32 _ _ (1091909 / 50000) (2183821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3017341184_3049341184 :
    ThetaLowerSegment 3017341184 3049341184 (301726405592907 / 100000)
      (304926605125579 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3017341184 cell3017472256)
                  (ThetaLowerSegment.join cell3017603328 cell3017734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3017865472 cell3017996544)
                  (ThetaLowerSegment.join cell3018127616 cell3018258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3018389760 cell3018520832)
                  (ThetaLowerSegment.join cell3018651904 cell3018782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3018914048 cell3019045120)
                  (ThetaLowerSegment.join cell3019176192 cell3019307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3019438336 cell3019569408)
                  (ThetaLowerSegment.join cell3019700480 cell3019831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3019962624 cell3020093696)
                  (ThetaLowerSegment.join cell3020224768 cell3020355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3020486912 cell3020617984)
                  (ThetaLowerSegment.join cell3020749056 cell3020880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3021011200 cell3021142272)
                  (ThetaLowerSegment.join cell3021273344 cell3021404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3021535488 cell3021666560)
                  (ThetaLowerSegment.join cell3021797632 cell3021928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3022059776 cell3022190848)
                  (ThetaLowerSegment.join cell3022321920 cell3022452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3022584064 cell3022715136)
                  (ThetaLowerSegment.join cell3022846208 cell3022977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3023108352 cell3023239424)
                  (ThetaLowerSegment.join cell3023370496 cell3023501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3023632640 cell3023763712)
                  (ThetaLowerSegment.join cell3023894784 cell3024025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3024156928 cell3024288000)
                  (ThetaLowerSegment.join cell3024419072 cell3024550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3024681216 cell3024812288)
                  (ThetaLowerSegment.join cell3024943360 cell3025074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3025205504 cell3025336576)
                  (ThetaLowerSegment.join cell3025467648 cell3025598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3025729792 cell3025860864)
                  (ThetaLowerSegment.join cell3025991936 cell3026123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3026254080 cell3026385152)
                  (ThetaLowerSegment.join cell3026516224 cell3026647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3026778368 cell3026909440)
                  (ThetaLowerSegment.join cell3027040512 cell3027171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3027302656 cell3027433728)
                  (ThetaLowerSegment.join cell3027564800 cell3027695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3027826944 cell3027958016)
                  (ThetaLowerSegment.join cell3028089088 cell3028220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3028351232 cell3028482304)
                  (ThetaLowerSegment.join cell3028613376 cell3028744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3028875520 cell3029006592)
                  (ThetaLowerSegment.join cell3029137664 cell3029268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3029399808 cell3029530880)
                  (ThetaLowerSegment.join cell3029661952 cell3029793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3029924096 cell3030055168)
                  (ThetaLowerSegment.join cell3030186240 cell3030317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3030448384 cell3030579456)
                  (ThetaLowerSegment.join cell3030710528 cell3030841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3030972672 cell3031103744)
                  (ThetaLowerSegment.join cell3031234816 cell3031365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3031496960 cell3031628032)
                  (ThetaLowerSegment.join cell3031759104 cell3031890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3032021248 cell3032152320)
                  (ThetaLowerSegment.join cell3032283392 cell3032414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3032545536 cell3032676608)
                  (ThetaLowerSegment.join cell3032807680 cell3032938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3033069824 cell3033200896)
                  (ThetaLowerSegment.join cell3033331968 cell3033463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3033594112 cell3033725184)
                  (ThetaLowerSegment.join cell3033856256 cell3033987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3034118400 cell3034249472)
                  (ThetaLowerSegment.join cell3034380544 cell3034511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3034642688 cell3034773760)
                  (ThetaLowerSegment.join cell3034904832 cell3035035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3035166976 cell3035298048)
                  (ThetaLowerSegment.join cell3035429120 cell3035560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3035691264 cell3035822336)
                  (ThetaLowerSegment.join cell3035953408 cell3036084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3036215552 cell3036346624)
                  (ThetaLowerSegment.join cell3036477696 cell3036608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3036739840 cell3036870912)
                  (ThetaLowerSegment.join cell3037001984 cell3037133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3037264128 cell3037395200)
                  (ThetaLowerSegment.join cell3037526272 cell3037657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3037788416 cell3037919488)
                  (ThetaLowerSegment.join cell3038050560 cell3038181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3038312704 cell3038443776)
                  (ThetaLowerSegment.join cell3038574848 cell3038705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3038836992 cell3038968064)
                  (ThetaLowerSegment.join cell3039099136 cell3039230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3039361280 cell3039492352)
                  (ThetaLowerSegment.join cell3039623424 cell3039754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3039885568 cell3040016640)
                  (ThetaLowerSegment.join cell3040147712 cell3040278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3040409856 cell3040540928)
                  (ThetaLowerSegment.join cell3040672000 cell3040803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3040934144 cell3041065216)
                  (ThetaLowerSegment.join cell3041196288 cell3041327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3041458432 cell3041589504)
                  (ThetaLowerSegment.join cell3041720576 cell3041851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3041982720 cell3042113792)
                  (ThetaLowerSegment.join cell3042244864 cell3042375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3042507008 cell3042638080)
                  (ThetaLowerSegment.join cell3042769152 cell3042900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3043031296 cell3043162368)
                  (ThetaLowerSegment.join cell3043293440 cell3043424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3043555584 cell3043686656)
                  (ThetaLowerSegment.join cell3043817728 cell3043948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3044079872 cell3044210944)
                  (ThetaLowerSegment.join cell3044342016 cell3044473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3044604160 cell3044735232)
                  (ThetaLowerSegment.join cell3044866304 cell3044997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3045128448 cell3045259520)
                  (ThetaLowerSegment.join cell3045390592 cell3045521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3045652736 cell3045783808)
                  (ThetaLowerSegment.join cell3045914880 cell3046045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3046177024 cell3046308096)
                  (ThetaLowerSegment.join cell3046439168 cell3046570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3046701312 cell3046832384)
                  (ThetaLowerSegment.join cell3046963456 cell3047094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3047225600 cell3047356672)
                  (ThetaLowerSegment.join cell3047487744 cell3047618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3047749888 cell3047880960)
                  (ThetaLowerSegment.join cell3048012032 cell3048143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3048274176 cell3048405248)
                  (ThetaLowerSegment.join cell3048536320 cell3048667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3048798464 cell3048929536)
                (ThetaLowerSegment.join cell3049060608 cell3049191680))
              (ThetaLowerSegment.join cell3049322752 cell3049339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
