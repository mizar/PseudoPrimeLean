/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3529341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3497341184 :
    ThetaLowerSegment 3497341184 3497472256 (349726131531189 / 100000)
      (349739272730689 / 100000) := by
  exact
    packedTile65536 3497341184 3497472256 14 5980 59138 32 _ _ (87901 / 4000) (274691 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497472256 :
    ThetaLowerSegment 3497472256 3497603328 (349739272730689 / 100000)
      (349752479879979 / 100000) := by
  exact
    packedTile65536 3497472256 3497603328 14 6010 59139 32 _ _ (2197529 / 100000) (549383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497603328 :
    ThetaLowerSegment 3497603328 3497734400 (349752479879979 / 100000) (17488282924269 / 5000) := by
  exact
    packedTile65536 3497603328 3497734400 14 5997 59140 32 _ _ (2197533 / 100000) (68673 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497734400 :
    ThetaLowerSegment 3497734400 3497865472 (17488282924269 / 5000) (174889358125117 / 50000) := by
  exact
    packedTile65536 3497734400 3497865472 14 5942 59141 32 _ _ (2197537 / 100000) (109877 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497865472 :
    ThetaLowerSegment 3497865472 3497996544 (174889358125117 / 50000)
      (174895894707847 / 50000) := by
  exact
    packedTile65536 3497865472 3497996544 14 5949 59142 32 _ _ (109877 / 5000) (2197543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3497996544 :
    ThetaLowerSegment 3497996544 3498127616 (174895894707847 / 50000)
      (174902408228263 / 50000) := by
  exact
    packedTile65536 3497996544 3498127616 14 5928 59143 32 _ _ (274693 / 12500) (2197547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3498127616 :
    ThetaLowerSegment 3498127616 3498258688 (174902408228263 / 50000)
      (174908986588201 / 50000) := by
  exact
    packedTile65536 3498127616 3498258688 14 5987 59144 32 _ _ (549387 / 25000) (2197551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3498258688 :
    ThetaLowerSegment 3498258688 3498389760 (174908986588201 / 50000)
      (174915519910297 / 50000) := by
  exact
    packedTile65536 3498258688 3498389760 14 5946 59146 32 _ _ (137347 / 6250) (439511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3498389760 :
    ThetaLowerSegment 3498389760 3498520832 (174915519910297 / 50000) (43730502322553 / 12500) := by
  exact
    packedTile65536 3498389760 3498520832 14 5906 59147 32 _ _ (439511 / 20000) (1098779 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3498520832 :
    ThetaLowerSegment 3498520832 3498651904 (43730502322553 / 12500)
      (349857148995449 / 100000) := by
  exact
    packedTile65536 3498520832 3498651904 14 5975 59148 32 _ _ (2197559 / 100000) (1098781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3498651904 :
    ThetaLowerSegment 3498651904 3498782976 (349857148995449 / 100000)
      (69974054568337 / 20000) := by
  exact
    packedTile65536 3498651904 3498782976 14 5972 59149 32 _ _ (2197563 / 100000) (1098783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3498782976 :
    ThetaLowerSegment 3498782976 3498914048 (69974054568337 / 20000) (174941640120379 / 50000) := by
  exact
    packedTile65536 3498782976 3498914048 14 5919 59150 32 _ _ (2197567 / 100000) (219757 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3498914048 :
    ThetaLowerSegment 3498914048 3499045120 (174941640120379 / 50000)
      (174948109766459 / 50000) := by
  exact
    packedTile65536 3498914048 3499045120 14 5888 59151 32 _ _ (219757 / 10000) (2197573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499045120 :
    ThetaLowerSegment 3499045120 3499176192 (174948109766459 / 50000)
      (174954724464199 / 50000) := by
  exact
    packedTile65536 3499045120 3499176192 14 6020 59152 32 _ _ (1098787 / 50000) (2197577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499176192 :
    ThetaLowerSegment 3499176192 3499307264 (174954724464199 / 50000)
      (174961238085391 / 50000) := by
  exact
    packedTile65536 3499176192 3499307264 14 5928 59153 32 _ _ (1098789 / 50000) (2197581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499307264 :
    ThetaLowerSegment 3499307264 3499438336 (174961238085391 / 50000) (34993545069491 / 10000) := by
  exact
    packedTile65536 3499307264 3499438336 14 5904 59154 32 _ _ (1098791 / 50000) (439517 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499438336 :
    ThetaLowerSegment 3499438336 3499569408 (34993545069491 / 10000) (6998971141837 / 2000) := by
  exact
    packedTile65536 3499438336 3499569408 14 5964 59156 32 _ _ (439517 / 20000) (549397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499569408 :
    ThetaLowerSegment 3499569408 3499700480 (6998971141837 / 2000) (17498083834909 / 5000) := by
  exact
    packedTile65536 3499569408 3499700480 14 5970 59157 32 _ _ (2197589 / 100000) (274699 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499700480 :
    ThetaLowerSegment 3499700480 3499831552 (17498083834909 / 5000) (349974789735611 / 100000) := by
  exact
    packedTile65536 3499700480 3499831552 14 5967 59158 32 _ _ (2197593 / 100000) (549399 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499831552 :
    ThetaLowerSegment 3499831552 3499962624 (349974789735611 / 100000)
      (34998799070079 / 10000) := by
  exact
    packedTile65536 3499831552 3499962624 14 6007 59159 32 _ _ (2197597 / 100000) (2747 / 125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3499962624 :
    ThetaLowerSegment 3499962624 3500093696 (34998799070079 / 10000) (35000110817519 / 10000) := by
  exact
    packedTile65536 3499962624 3500093696 14 5969 59160 32 _ _ (2747 / 125) (2197603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3500093696 :
    ThetaLowerSegment 3500093696 3500224768 (35000110817519 / 10000) (175007138109179 / 50000) := by
  exact
    packedTile65536 3500093696 3500224768 14 5992 59161 32 _ _ (549401 / 25000) (2197607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3500224768 :
    ThetaLowerSegment 3500224768 3500355840 (175007138109179 / 50000) (35002736077639 / 10000) := by
  exact
    packedTile65536 3500224768 3500355840 14 5954 59162 32 _ _ (274701 / 12500) (2197611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3500355840 :
    ThetaLowerSegment 3500355840 3500486912 (35002736077639 / 10000) (175020282014643 / 50000) := by
  exact
    packedTile65536 3500355840 3500486912 14 6008 59163 32 _ _ (549403 / 25000) (439523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3500486912 :
    ThetaLowerSegment 3500486912 3500617984 (175020282014643 / 50000)
      (350053760707361 / 100000) := by
  exact
    packedTile65536 3500486912 3500617984 14 6005 59164 32 _ _ (439523 / 20000) (1098809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3500617984 :
    ThetaLowerSegment 3500617984 3500749056 (350053760707361 / 100000) (21879171652377 / 6250) := by
  exact
    packedTile65536 3500617984 3500749056 14 5909 59166 32 _ _ (2197619 / 100000) (1098811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3500749056 :
    ThetaLowerSegment 3500749056 3500880128 (21879171652377 / 6250) (43759993719627 / 12500) := by
  exact
    packedTile65536 3500749056 3500880128 14 6008 59167 32 _ _ (2197623 / 100000) (1098813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3500880128 :
    ThetaLowerSegment 3500880128 3501011200 (43759993719627 / 12500)
      (350092935534959 / 100000) := by
  exact
    packedTile65536 3500880128 3501011200 14 5909 59168 32 _ _ (2197627 / 100000) (219763 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501011200 :
    ThetaLowerSegment 3501011200 3501142272 (350092935534959 / 100000)
      (350105921330629 / 100000) := by
  exact
    packedTile65536 3501011200 3501142272 14 5909 59169 32 _ _ (219763 / 10000) (2197633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501142272 :
    ThetaLowerSegment 3501142272 3501273344 (350105921330629 / 100000)
      (350119287340617 / 100000) := by
  exact
    packedTile65536 3501142272 3501273344 14 6082 59170 32 _ _ (1098817 / 50000) (2197637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501273344 :
    ThetaLowerSegment 3501273344 3501404416 (350119287340617 / 100000)
      (70026422551197 / 20000) := by
  exact
    packedTile65536 3501273344 3501404416 14 5836 59171 32 _ _ (1098819 / 50000) (2197641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501404416 :
    ThetaLowerSegment 3501404416 3501535488 (70026422551197 / 20000) (43768140074133 / 12500) := by
  exact
    packedTile65536 3501404416 3501535488 14 5919 59172 32 _ _ (2197641 / 100000) (549411 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501535488 :
    ThetaLowerSegment 3501535488 3501666560 (43768140074133 / 12500)
      (350158449309989 / 100000) := by
  exact
    packedTile65536 3501535488 3501666560 14 6065 59173 32 _ _ (439529 / 20000) (137353 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501666560 :
    ThetaLowerSegment 3501666560 3501797632 (350158449309989 / 100000)
      (175085765957243 / 50000) := by
  exact
    packedTile65536 3501666560 3501797632 14 5953 59174 32 _ _ (2197649 / 100000) (549413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501797632 :
    ThetaLowerSegment 3501797632 3501928704 (175085765957243 / 50000) (17509231276553 / 5000) := by
  exact
    packedTile65536 3501797632 3501928704 14 5958 59175 32 _ _ (2197653 / 100000) (274707 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3501928704 :
    ThetaLowerSegment 3501928704 3502059776 (17509231276553 / 5000) (87549422099581 / 25000) := by
  exact
    packedTile65536 3501928704 3502059776 14 5944 59177 32 _ _ (274707 / 12500) (2197659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502059776 :
    ThetaLowerSegment 3502059776 3502190848 (87549422099581 / 25000) (87552718589581 / 25000) := by
  exact
    packedTile65536 3502059776 3502190848 14 6000 59178 32 _ _ (109883 / 5000) (2197663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502190848 :
    ThetaLowerSegment 3502190848 3502321920 (87552718589581 / 25000) (87556029370397 / 25000) := by
  exact
    packedTile65536 3502190848 3502321920 14 6026 59179 32 _ _ (68677 / 3125) (2197667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502321920 :
    ThetaLowerSegment 3502321920 3502452992 (87556029370397 / 25000) (87559297302713 / 25000) := by
  exact
    packedTile65536 3502321920 3502452992 14 5948 59180 32 _ _ (549417 / 25000) (2197671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502452992 :
    ThetaLowerSegment 3502452992 3502584064 (87559297302713 / 25000)
      (350250219202211 / 100000) := by
  exact
    packedTile65536 3502452992 3502584064 14 5929 59181 32 _ _ (2197671 / 100000) (1098837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502584064 :
    ThetaLowerSegment 3502584064 3502715136 (350250219202211 / 100000)
      (175131659771443 / 50000) := by
  exact
    packedTile65536 3502584064 3502715136 14 5961 59182 32 _ _ (87907 / 4000) (1098839 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502715136 :
    ThetaLowerSegment 3502715136 3502846208 (175131659771443 / 50000) (70055279586123 / 20000) := by
  exact
    packedTile65536 3502715136 3502846208 14 5951 59183 32 _ _ (2197679 / 100000) (1098841 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502846208 :
    ThetaLowerSegment 3502846208 3502977280 (70055279586123 / 20000)
      (350289478539831 / 100000) := by
  exact
    packedTile65536 3502846208 3502977280 14 5952 59184 32 _ _ (2197683 / 100000) (1098843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3502977280 :
    ThetaLowerSegment 3502977280 3503108352 (350289478539831 / 100000)
      (350302611911367 / 100000) := by
  exact
    packedTile65536 3502977280 3503108352 14 5976 59185 32 _ _ (1098843 / 50000) (2197689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503108352 :
    ThetaLowerSegment 3503108352 3503239424 (350302611911367 / 100000)
      (350315793655987 / 100000) := by
  exact
    packedTile65536 3503108352 3503239424 14 5998 59187 32 _ _ (219769 / 10000) (2197693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503239424 :
    ThetaLowerSegment 3503239424 3503370496 (350315793655987 / 100000)
      (350328839167571 / 100000) := by
  exact
    packedTile65536 3503239424 3503370496 14 5936 59188 32 _ _ (1098847 / 50000) (2197697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503370496 :
    ThetaLowerSegment 3503370496 3503501568 (350328839167571 / 100000)
      (350342012169383 / 100000) := by
  exact
    packedTile65536 3503370496 3503501568 14 5994 59189 32 _ _ (1098849 / 50000) (2197701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503501568 :
    ThetaLowerSegment 3503501568 3503632640 (350342012169383 / 100000)
      (350355057722519 / 100000) := by
  exact
    packedTile65536 3503501568 3503632640 14 5936 59190 32 _ _ (2197701 / 100000) (274713 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503632640 :
    ThetaLowerSegment 3503632640 3503763712 (350355057722519 / 100000)
      (87592037362801 / 25000) := by
  exact
    packedTile65536 3503632640 3503763712 14 5957 59191 32 _ _ (439541 / 20000) (549427 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503763712 :
    ThetaLowerSegment 3503763712 3503894784 (87592037362801 / 25000)
      (350381030223653 / 100000) := by
  exact
    packedTile65536 3503763712 3503894784 14 5861 59192 32 _ _ (2197709 / 100000) (137357 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3503894784 :
    ThetaLowerSegment 3503894784 3504025856 (350381030223653 / 100000)
      (350394216501653 / 100000) := by
  exact
    packedTile65536 3503894784 3504025856 14 6000 59193 32 _ _ (2197713 / 100000) (549429 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504025856 :
    ThetaLowerSegment 3504025856 3504156928 (350394216501653 / 100000)
      (350407453345121 / 100000) := by
  exact
    packedTile65536 3504025856 3504156928 14 6023 59194 32 _ _ (549429 / 25000) (2197719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504156928 :
    ThetaLowerSegment 3504156928 3504288000 (350407453345121 / 100000)
      (350420709992161 / 100000) := by
  exact
    packedTile65536 3504156928 3504288000 14 6032 59195 32 _ _ (54943 / 2500) (2197723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504288000 :
    ThetaLowerSegment 3504288000 3504419072 (350420709992161 / 100000)
      (350433683156933 / 100000) := by
  exact
    packedTile65536 3504288000 3504419072 14 5903 59197 32 _ _ (549431 / 25000) (2197727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504419072 :
    ThetaLowerSegment 3504419072 3504550144 (350433683156933 / 100000)
      (350446957434053 / 100000) := by
  exact
    packedTile65536 3504419072 3504550144 14 6040 59198 32 _ _ (68679 / 3125) (2197731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504550144 :
    ThetaLowerSegment 3504550144 3504681216 (350446957434053 / 100000)
      (350460077888123 / 100000) := by
  exact
    packedTile65536 3504550144 3504681216 14 5970 59199 32 _ _ (2197731 / 100000) (1098867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504681216 :
    ThetaLowerSegment 3504681216 3504812288 (350460077888123 / 100000)
      (350473185179663 / 100000) := by
  exact
    packedTile65536 3504681216 3504812288 14 5964 59200 32 _ _ (439547 / 20000) (1098869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504812288 :
    ThetaLowerSegment 3504812288 3504943360 (350473185179663 / 100000)
      (350486261726713 / 100000) := by
  exact
    packedTile65536 3504812288 3504943360 14 5950 59201 32 _ _ (2197739 / 100000) (1098871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3504943360 :
    ThetaLowerSegment 3504943360 3505074432 (350486261726713 / 100000)
      (70099900186109 / 20000) := by
  exact
    packedTile65536 3504943360 3505074432 14 6024 59202 32 _ _ (2197743 / 100000) (1098873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505074432 :
    ThetaLowerSegment 3505074432 3505205504 (70099900186109 / 20000)
      (350512601694451 / 100000) := by
  exact
    packedTile65536 3505074432 3505205504 14 5961 59203 32 _ _ (1098873 / 50000) (2197749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505205504 :
    ThetaLowerSegment 3505205504 3505336576 (350512601694451 / 100000)
      (350525733250701 / 100000) := by
  exact
    packedTile65536 3505205504 3505336576 14 5975 59204 32 _ _ (8791 / 400) (2197753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505336576 :
    ThetaLowerSegment 3505336576 3505467648 (350525733250701 / 100000)
      (70107755823689 / 20000) := by
  exact
    packedTile65536 3505336576 3505467648 14 5936 59205 32 _ _ (1098877 / 50000) (2197757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505467648 :
    ThetaLowerSegment 3505467648 3505598720 (70107755823689 / 20000)
      (350552189831659 / 100000) := by
  exact
    packedTile65536 3505467648 3505598720 14 6102 59206 32 _ _ (2197757 / 100000) (13736 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505598720 :
    ThetaLowerSegment 3505598720 3505729792 (350552189831659 / 100000)
      (350565358815571 / 100000) := by
  exact
    packedTile65536 3505598720 3505729792 14 5992 59208 32 _ _ (2197761 / 100000) (549441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505729792 :
    ThetaLowerSegment 3505729792 3505860864 (350565358815571 / 100000)
      (175289214462013 / 50000) := by
  exact
    packedTile65536 3505729792 3505860864 14 5947 59209 32 _ _ (439553 / 20000) (274721 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505860864 :
    ThetaLowerSegment 3505860864 3505991936 (175289214462013 / 50000)
      (350591556198263 / 100000) := by
  exact
    packedTile65536 3505860864 3505991936 14 5973 59210 32 _ _ (2197769 / 100000) (549443 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3505991936 :
    ThetaLowerSegment 3505991936 3506123008 (350591556198263 / 100000)
      (70120942412291 / 20000) := by
  exact
    packedTile65536 3505991936 3506123008 14 5986 59211 32 _ _ (549443 / 25000) (87911 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3506123008 :
    ThetaLowerSegment 3506123008 3506254080 (70120942412291 / 20000)
      (350617729488703 / 100000) := by
  exact
    packedTile65536 3506123008 3506254080 14 5923 59212 32 _ _ (137361 / 6250) (2197779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3506254080 :
    ThetaLowerSegment 3506254080 3506385152 (350617729488703 / 100000)
      (350630870015323 / 100000) := by
  exact
    packedTile65536 3506254080 3506385152 14 5979 59213 32 _ _ (109889 / 5000) (2197783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3506385152 :
    ThetaLowerSegment 3506385152 3506516224 (350630870015323 / 100000)
      (350643957819043 / 100000) := by
  exact
    packedTile65536 3506385152 3506516224 14 5955 59214 32 _ _ (274723 / 12500) (2197787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3506516224 :
    ThetaLowerSegment 3506516224 3506647296 (350643957819043 / 100000)
      (350657206079079 / 100000) := by
  exact
    packedTile65536 3506516224 3506647296 14 6028 59215 32 _ _ (2197787 / 100000) (219779 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3506647296 :
    ThetaLowerSegment 3506647296 3506778368 (350657206079079 / 100000)
      (175335184324689 / 50000) := by
  exact
    packedTile65536 3506647296 3506778368 14 5989 59216 32 _ _ (2197791 / 100000) (1098897 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3506778368 :
    ThetaLowerSegment 3506778368 3506909440 (175335184324689 / 50000)
      (175341659028759 / 50000) := by
  exact
    packedTile65536 3506778368 3506909440 14 5892 59218 32 _ _ (439559 / 20000) (1098899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3506909440 :
    ThetaLowerSegment 3506909440 3507040512 (175341659028759 / 50000) (21918526882897 / 6250) := by
  exact
    packedTile65536 3506909440 3507040512 14 5966 59219 32 _ _ (2197799 / 100000) (1098901 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507040512 :
    ThetaLowerSegment 3507040512 3507171584 (21918526882897 / 6250) (87677398740083 / 25000) := by
  exact
    packedTile65536 3507040512 3507171584 14 5990 59220 32 _ _ (1098901 / 50000) (439561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507171584 :
    ThetaLowerSegment 3507171584 3507302656 (87677398740083 / 25000) (17536133375521 / 5000) := by
  exact
    packedTile65536 3507171584 3507302656 14 5948 59221 32 _ _ (1098903 / 50000) (2197809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507302656 :
    ThetaLowerSegment 3507302656 3507433728 (17536133375521 / 5000) (7014713702781 / 2000) := by
  exact
    packedTile65536 3507302656 3507433728 14 5923 59222 32 _ _ (219781 / 10000) (2197813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507433728 :
    ThetaLowerSegment 3507433728 3507564800 (7014713702781 / 2000) (21921816726781 / 6250) := by
  exact
    packedTile65536 3507433728 3507564800 14 6089 59223 32 _ _ (1098907 / 50000) (2197817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507564800 :
    ThetaLowerSegment 3507564800 3507695872 (21921816726781 / 6250) (175381147045601 / 50000) := by
  exact
    packedTile65536 3507564800 3507695872 14 6018 59224 32 _ _ (2197817 / 100000) (109891 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507695872 :
    ThetaLowerSegment 3507695872 3507826944 (175381147045601 / 50000) (87693844979359 / 25000) := by
  exact
    packedTile65536 3507695872 3507826944 14 5954 59225 32 _ _ (2197821 / 100000) (68682 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507826944 :
    ThetaLowerSegment 3507826944 3507958016 (87693844979359 / 25000) (175394298818493 / 50000) := by
  exact
    packedTile65536 3507826944 3507958016 14 6014 59226 32 _ _ (87913 / 4000) (549457 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3507958016 :
    ThetaLowerSegment 3507958016 3508089088 (175394298818493 / 50000)
      (175400812081771 / 50000) := by
  exact
    packedTile65536 3507958016 3508089088 14 5927 59228 32 _ _ (549457 / 25000) (2197831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3508089088 :
    ThetaLowerSegment 3508089088 3508220160 (175400812081771 / 50000)
      (175407325356903 / 50000) := by
  exact
    packedTile65536 3508089088 3508220160 14 5927 59229 32 _ _ (274729 / 12500) (439567 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3508220160 :
    ThetaLowerSegment 3508220160 3508351232 (175407325356903 / 50000)
      (175413925458411 / 50000) := by
  exact
    packedTile65536 3508220160 3508351232 14 6006 59230 32 _ _ (549459 / 25000) (2197839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3508351232 :
    ThetaLowerSegment 3508351232 3508482304 (175413925458411 / 50000)
      (175420350843651 / 50000) := by
  exact
    packedTile65536 3508351232 3508482304 14 5847 59231 32 _ _ (27473 / 1250) (2197843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3508482304 :
    ThetaLowerSegment 3508482304 3508613376 (175420350843651 / 50000)
      (350853807425111 / 100000) := by
  exact
    packedTile65536 3508482304 3508613376 14 5963 59232 32 _ _ (2197843 / 100000) (1098923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3508613376 :
    ThetaLowerSegment 3508613376 3508744448 (350853807425111 / 100000)
      (350866875823373 / 100000) := by
  exact
    packedTile65536 3508613376 3508744448 14 5946 59233 32 _ _ (2197847 / 100000) (43957 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3508744448 :
    ThetaLowerSegment 3508744448 3508875520 (350866875823373 / 100000)
      (350879996993843 / 100000) := by
  exact
    packedTile65536 3508744448 3508875520 14 5970 59234 32 _ _ (2197851 / 100000) (1098927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3508875520 :
    ThetaLowerSegment 3508875520 3509006592 (350879996993843 / 100000)
      (350893144562453 / 100000) := by
  exact
    packedTile65536 3508875520 3509006592 14 5982 59235 32 _ _ (439571 / 20000) (1098929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509006592 :
    ThetaLowerSegment 3509006592 3509137664 (350893144562453 / 100000)
      (70181261506803 / 20000) := by
  exact
    packedTile65536 3509006592 3509137664 14 5989 59236 32 _ _ (1098929 / 50000) (2197861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509137664 :
    ThetaLowerSegment 3509137664 3509268736 (70181261506803 / 20000)
      (350919536465393 / 100000) := by
  exact
    packedTile65536 3509137664 3509268736 14 6019 59237 32 _ _ (1098931 / 50000) (439573 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509268736 :
    ThetaLowerSegment 3509268736 3509399808 (350919536465393 / 100000)
      (350932582997969 / 100000) := by
  exact
    packedTile65536 3509268736 3509399808 14 5936 59239 32 _ _ (1098933 / 50000) (2197869 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509399808 :
    ThetaLowerSegment 3509399808 3509530880 (350932582997969 / 100000)
      (350945710875479 / 100000) := by
  exact
    packedTile65536 3509399808 3509530880 14 5973 59240 32 _ _ (219787 / 10000) (2197873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509530880 :
    ThetaLowerSegment 3509530880 3509661952 (350945710875479 / 100000)
      (70191718961401 / 20000) := by
  exact
    packedTile65536 3509530880 3509661952 14 5862 59241 32 _ _ (2197873 / 100000) (549469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509661952 :
    ThetaLowerSegment 3509661952 3509793024 (70191718961401 / 20000)
      (350971856796823 / 100000) := by
  exact
    packedTile65536 3509661952 3509793024 14 6034 59242 32 _ _ (2197877 / 100000) (54947 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509793024 :
    ThetaLowerSegment 3509793024 3509924096 (350971856796823 / 100000)
      (43873137378731 / 12500) := by
  exact
    packedTile65536 3509793024 3509924096 14 6025 59243 32 _ _ (2197881 / 100000) (549471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3509924096 :
    ThetaLowerSegment 3509924096 3510055168 (43873137378731 / 12500) (175499162950889 / 50000) := by
  exact
    packedTile65536 3509924096 3510055168 14 6018 59244 32 _ _ (439577 / 20000) (68684 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510055168 :
    ThetaLowerSegment 3510055168 3510186240 (175499162950889 / 50000)
      (175505754417001 / 50000) := by
  exact
    packedTile65536 3510055168 3510186240 14 5998 59245 32 _ _ (68684 / 3125) (2197891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510186240 :
    ThetaLowerSegment 3510186240 3510317312 (175505754417001 / 50000)
      (175512287650971 / 50000) := by
  exact
    packedTile65536 3510186240 3510317312 14 5945 59246 32 _ _ (549473 / 25000) (439579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510317312 :
    ThetaLowerSegment 3510317312 3510448384 (175512287650971 / 50000)
      (175518740673627 / 50000) := by
  exact
    packedTile65536 3510317312 3510448384 14 5872 59247 32 _ _ (274737 / 12500) (2197899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510448384 :
    ThetaLowerSegment 3510448384 3510579456 (175518740673627 / 50000)
      (175525347558021 / 50000) := by
  exact
    packedTile65536 3510448384 3510579456 14 6012 59249 32 _ _ (2197899 / 100000) (1098951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510579456 :
    ThetaLowerSegment 3510579456 3510710528 (175525347558021 / 50000) (43882955095589 / 12500) := by
  exact
    packedTile65536 3510579456 3510710528 14 5890 59250 32 _ _ (2197903 / 100000) (1098953 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510710528 :
    ThetaLowerSegment 3510710528 3510841600 (43882955095589 / 12500)
      (351076777654851 / 100000) := by
  exact
    packedTile65536 3510710528 3510841600 14 5977 59251 32 _ _ (2197907 / 100000) (219791 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510841600 :
    ThetaLowerSegment 3510841600 3510972672 (351076777654851 / 100000)
      (351089934350097 / 100000) := by
  exact
    packedTile65536 3510841600 3510972672 14 5986 59252 32 _ _ (2197911 / 100000) (1098957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3510972672 :
    ThetaLowerSegment 3510972672 3511103744 (351089934350097 / 100000)
      (351103141615323 / 100000) := by
  exact
    packedTile65536 3510972672 3511103744 14 6009 59253 32 _ _ (1098957 / 50000) (2197917 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511103744 :
    ThetaLowerSegment 3511103744 3511234816 (351103141615323 / 100000)
      (351116267581619 / 100000) := by
  exact
    packedTile65536 3511103744 3511234816 14 5972 59254 32 _ _ (1098959 / 50000) (2197921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511234816 :
    ThetaLowerSegment 3511234816 3511365888 (351116267581619 / 100000)
      (351129244113107 / 100000) := by
  exact
    packedTile65536 3511234816 3511365888 14 5904 59255 32 _ _ (1098961 / 50000) (87917 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511365888 :
    ThetaLowerSegment 3511365888 3511496960 (351129244113107 / 100000)
      (351142453648367 / 100000) := by
  exact
    packedTile65536 3511365888 3511496960 14 6010 59256 32 _ _ (1098963 / 50000) (2197929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511496960 :
    ThetaLowerSegment 3511496960 3511628032 (351142453648367 / 100000)
      (70231124727787 / 20000) := by
  exact
    packedTile65536 3511496960 3511628032 14 5992 59257 32 _ _ (2197929 / 100000) (549483 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511628032 :
    ThetaLowerSegment 3511628032 3511759104 (70231124727787 / 20000) (175584360560841 / 50000) := by
  exact
    packedTile65536 3511628032 3511759104 14 5959 59258 32 _ _ (2197933 / 100000) (137371 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511759104 :
    ThetaLowerSegment 3511759104 3511890176 (175584360560841 / 50000) (87795478284889 / 25000) := by
  exact
    packedTile65536 3511759104 3511890176 14 6002 59260 32 _ _ (2197937 / 100000) (109897 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3511890176 :
    ThetaLowerSegment 3511890176 3512021248 (87795478284889 / 25000) (175597530611309 / 50000) := by
  exact
    packedTile65536 3511890176 3512021248 14 5982 59261 32 _ _ (2197941 / 100000) (274743 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512021248 :
    ThetaLowerSegment 3512021248 3512152320 (175597530611309 / 50000)
      (175604132136113 / 50000) := by
  exact
    packedTile65536 3512021248 3512152320 14 6007 59262 32 _ _ (274743 / 12500) (2197947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512152320 :
    ThetaLowerSegment 3512152320 3512283392 (175604132136113 / 50000)
      (175610644656037 / 50000) := by
  exact
    packedTile65536 3512152320 3512283392 14 5926 59263 32 _ _ (549487 / 25000) (2197951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512283392 :
    ThetaLowerSegment 3512283392 3512414464 (175610644656037 / 50000) (35123452757697 / 10000) := by
  exact
    packedTile65536 3512283392 3512414464 14 6023 59264 32 _ _ (68686 / 3125) (439591 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512414464 :
    ThetaLowerSegment 3512414464 3512545536 (35123452757697 / 10000) (70249503058613 / 20000) := by
  exact
    packedTile65536 3512414464 3512545536 14 5909 59265 32 _ _ (439591 / 20000) (1098979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512545536 :
    ThetaLowerSegment 3512545536 3512676608 (70249503058613 / 20000) (175630341632717 / 50000) := by
  exact
    packedTile65536 3512545536 3512676608 14 5991 59266 32 _ _ (2197959 / 100000) (1098981 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512676608 :
    ThetaLowerSegment 3512676608 3512807680 (175630341632717 / 50000) (43909210252327 / 12500) := by
  exact
    packedTile65536 3512676608 3512807680 14 5914 59267 32 _ _ (2197963 / 100000) (1098983 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512807680 :
    ThetaLowerSegment 3512807680 3512938752 (43909210252327 / 12500) (175643318418057 / 50000) := by
  exact
    packedTile65536 3512807680 3512938752 14 5894 59268 32 _ _ (2197967 / 100000) (219797 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3512938752 :
    ThetaLowerSegment 3512938752 3513069824 (175643318418057 / 50000)
      (175649839795047 / 50000) := by
  exact
    packedTile65536 3512938752 3513069824 14 5934 59270 32 _ _ (219797 / 10000) (2197973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513069824 :
    ThetaLowerSegment 3513069824 3513200896 (175649839795047 / 50000)
      (175656409539333 / 50000) := by
  exact
    packedTile65536 3513069824 3513200896 14 5978 59271 32 _ _ (1098987 / 50000) (2197977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513200896 :
    ThetaLowerSegment 3513200896 3513331968 (175656409539333 / 50000)
      (175662959513773 / 50000) := by
  exact
    packedTile65536 3513200896 3513331968 14 5960 59272 32 _ _ (1098989 / 50000) (2197981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513331968 :
    ThetaLowerSegment 3513331968 3513463040 (175662959513773 / 50000) (43917386441709 / 12500) := by
  exact
    packedTile65536 3513331968 3513463040 14 5993 59273 32 _ _ (1098991 / 50000) (439597 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513463040 :
    ThetaLowerSegment 3513463040 3513594112 (43917386441709 / 12500)
      (351352272849717 / 100000) := by
  exact
    packedTile65536 3513463040 3513594112 14 5997 59274 32 _ _ (439597 / 20000) (549497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513594112 :
    ThetaLowerSegment 3513594112 3513725184 (351352272849717 / 100000) (21960343359597 / 6250) := by
  exact
    packedTile65536 3513594112 3513725184 14 6015 59275 32 _ _ (2197989 / 100000) (274749 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513725184 :
    ThetaLowerSegment 3513725184 3513856256 (21960343359597 / 6250) (21961156617007 / 6250) := by
  exact
    packedTile65536 3513725184 3513856256 14 5920 59276 32 _ _ (2197993 / 100000) (549499 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513856256 :
    ThetaLowerSegment 3513856256 3513987328 (21961156617007 / 6250) (21961973172521 / 6250) := by
  exact
    packedTile65536 3513856256 3513987328 14 5944 59277 32 _ _ (549499 / 25000) (2197999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3513987328 :
    ThetaLowerSegment 3513987328 3514118400 (21961973172521 / 6250) (10981404824448 / 3125) := by
  exact
    packedTile65536 3513987328 3514118400 14 6089 59278 32 _ _ (1099 / 50) (2198003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3514118400 :
    ThetaLowerSegment 3514118400 3514249472 (10981404824448 / 3125) (4392725571177 / 1250) := by
  exact
    packedTile65536 3514118400 3514249472 14 5956 59280 32 _ _ (549501 / 25000) (2198007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3514249472 :
    ThetaLowerSegment 3514249472 3514380544 (4392725571177 / 1250) (43928901195509 / 12500) := by
  exact
    packedTile65536 3514249472 3514380544 14 5989 59281 32 _ _ (274751 / 12500) (2198011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3514380544 :
    ThetaLowerSegment 3514380544 3514511616 (43928901195509 / 12500)
      (351444122878697 / 100000) := by
  exact
    packedTile65536 3514380544 3514511616 14 5875 59282 32 _ _ (2198011 / 100000) (1099007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3514511616 :
    ThetaLowerSegment 3514511616 3514642688 (351444122878697 / 100000)
      (351457284592517 / 100000) := by
  exact
    packedTile65536 3514511616 3514642688 14 5988 59283 32 _ _ (439603 / 20000) (1099009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3514642688 :
    ThetaLowerSegment 3514642688 3514773760 (351457284592517 / 100000)
      (175735208878021 / 50000) := by
  exact
    packedTile65536 3514642688 3514773760 14 5975 59284 32 _ _ (2198019 / 100000) (1099011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3514773760 :
    ThetaLowerSegment 3514773760 3514904832 (175735208878021 / 50000)
      (351483656448571 / 100000) := by
  exact
    packedTile65536 3514773760 3514904832 14 6023 59285 32 _ _ (2198023 / 100000) (1099013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3514904832 :
    ThetaLowerSegment 3514904832 3515035904 (351483656448571 / 100000) (14059867541789 / 4000) := by
  exact
    packedTile65536 3514904832 3515035904 14 5929 59286 32 _ _ (1099013 / 50000) (2198029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515035904 :
    ThetaLowerSegment 3515035904 3515166976 (14059867541789 / 4000) (14060392431353 / 4000) := by
  exact
    packedTile65536 3515035904 3515166976 14 5970 59287 32 _ _ (219803 / 10000) (2198033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515166976 :
    ThetaLowerSegment 3515166976 3515298048 (14060392431353 / 4000) (351522755006051 / 100000) := by
  exact
    packedTile65536 3515166976 3515298048 14 5889 59288 32 _ _ (1099017 / 50000) (2198037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515298048 :
    ThetaLowerSegment 3515298048 3515429120 (351522755006051 / 100000)
      (70307203153861 / 20000) := by
  exact
    packedTile65536 3515298048 3515429120 14 6033 59289 32 _ _ (1099019 / 50000) (2198041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515429120 :
    ThetaLowerSegment 3515429120 3515560192 (70307203153861 / 20000) (175774576730181 / 50000) := by
  exact
    packedTile65536 3515429120 3515560192 14 5977 59291 32 _ _ (2198041 / 100000) (549511 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515560192 :
    ThetaLowerSegment 3515560192 3515691264 (175774576730181 / 50000) (87890560155073 / 25000) := by
  exact
    packedTile65536 3515560192 3515691264 14 5954 59292 32 _ _ (439609 / 20000) (68689 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515691264 :
    ThetaLowerSegment 3515691264 3515822336 (87890560155073 / 25000)
      (351575215703539 / 100000) := by
  exact
    packedTile65536 3515691264 3515822336 14 5903 59293 32 _ _ (2198049 / 100000) (549513 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515822336 :
    ThetaLowerSegment 3515822336 3515953408 (351575215703539 / 100000)
      (351588353460343 / 100000) := by
  exact
    packedTile65536 3515822336 3515953408 14 5977 59294 32 _ _ (549513 / 25000) (439611 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3515953408 :
    ThetaLowerSegment 3515953408 3516084480 (351588353460343 / 100000)
      (351601598945799 / 100000) := by
  exact
    packedTile65536 3515953408 3516084480 14 6026 59295 32 _ _ (274757 / 12500) (2198059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3516084480 :
    ThetaLowerSegment 3516084480 3516215552 (351601598945799 / 100000)
      (351614789503859 / 100000) := by
  exact
    packedTile65536 3516084480 3516215552 14 6001 59296 32 _ _ (109903 / 5000) (2198063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3516215552 :
    ThetaLowerSegment 3516215552 3516346624 (351614789503859 / 100000)
      (70325595137959 / 20000) := by
  exact
    packedTile65536 3516215552 3516346624 14 5999 59297 32 _ _ (137379 / 6250) (2198067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3516346624 :
    ThetaLowerSegment 3516346624 3516477696 (70325595137959 / 20000) (175820591937199 / 50000) := by
  exact
    packedTile65536 3516346624 3516477696 14 6009 59298 32 _ _ (2198067 / 100000) (219807 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3516477696 :
    ThetaLowerSegment 3516477696 3516608768 (175820591937199 / 50000)
      (351654295367913 / 100000) := by
  exact
    packedTile65536 3516477696 3516608768 14 5965 59299 32 _ _ (2198071 / 100000) (1099037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3516608768 :
    ThetaLowerSegment 3516608768 3516739840 (351654295367913 / 100000)
      (87916853919397 / 25000) := by
  exact
    packedTile65536 3516608768 3516739840 14 5969 59301 32 _ _ (87923 / 4000) (1099039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3516739840 :
    ThetaLowerSegment 3516739840 3516870912 (87916853919397 / 25000) (10990014758339 / 3125) := by
  exact
    packedTile65536 3516739840 3516870912 14 5940 59302 32 _ _ (2198079 / 100000) (1099041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3516870912 :
    ThetaLowerSegment 3516870912 3517001984 (10990014758339 / 3125) (17584679301203 / 5000) := by
  exact
    packedTile65536 3516870912 3517001984 14 5966 59303 32 _ _ (1099041 / 50000) (439617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517001984 :
    ThetaLowerSegment 3517001984 3517133056 (17584679301203 / 5000) (175853335615009 / 50000) := by
  exact
    packedTile65536 3517001984 3517133056 14 5953 59304 32 _ _ (1099043 / 50000) (2198089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517133056 :
    ThetaLowerSegment 3517133056 3517264128 (175853335615009 / 50000)
      (175859923290739 / 50000) := by
  exact
    packedTile65536 3517133056 3517264128 14 5994 59305 32 _ _ (219809 / 10000) (2198093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517264128 :
    ThetaLowerSegment 3517264128 3517395200 (175859923290739 / 50000) (70346589003533 / 20000) := by
  exact
    packedTile65536 3517264128 3517395200 14 5959 59306 32 _ _ (2198093 / 100000) (137381 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517395200 :
    ThetaLowerSegment 3517395200 3517526272 (70346589003533 / 20000) (87936473501773 / 25000) := by
  exact
    packedTile65536 3517395200 3517526272 14 5891 59307 32 _ _ (2198097 / 100000) (21981 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517526272 :
    ThetaLowerSegment 3517526272 3517657344 (87936473501773 / 25000) (43969877633283 / 12500) := by
  exact
    packedTile65536 3517526272 3517657344 14 5972 59308 32 _ _ (2198101 / 100000) (274763 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517657344 :
    ThetaLowerSegment 3517657344 3517788416 (43969877633283 / 12500) (10992876607272 / 3125) := by
  exact
    packedTile65536 3517657344 3517788416 14 5928 59309 32 _ _ (439621 / 20000) (549527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517788416 :
    ThetaLowerSegment 3517788416 3517919488 (10992876607272 / 3125) (43973130281373 / 12500) := by
  exact
    packedTile65536 3517788416 3517919488 14 5910 59310 32 _ _ (549527 / 25000) (2198111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3517919488 :
    ThetaLowerSegment 3517919488 3518050560 (43973130281373 / 12500) (43974770897217 / 12500) := by
  exact
    packedTile65536 3517919488 3518050560 14 5971 59312 32 _ _ (68691 / 3125) (439623 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518050560 :
    ThetaLowerSegment 3518050560 3518181632 (43974770897217 / 12500) (10994101436498 / 3125) := by
  exact
    packedTile65536 3518050560 3518181632 14 5950 59313 32 _ _ (549529 / 25000) (2198119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518181632 :
    ThetaLowerSegment 3518181632 3518312704 (10994101436498 / 3125) (21989014803571 / 6250) := by
  exact
    packedTile65536 3518181632 3518312704 14 5910 59314 32 _ _ (54953 / 2500) (2198123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518312704 :
    ThetaLowerSegment 3518312704 3518443776 (21989014803571 / 6250) (351837331075847 / 100000) := by
  exact
    packedTile65536 3518312704 3518443776 14 5957 59315 32 _ _ (2198123 / 100000) (1099063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518443776 :
    ThetaLowerSegment 3518443776 3518574848 (351837331075847 / 100000)
      (351850295628893 / 100000) := by
  exact
    packedTile65536 3518443776 3518574848 14 5898 59316 32 _ _ (2198127 / 100000) (219813 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518574848 :
    ThetaLowerSegment 3518574848 3518705920 (351850295628893 / 100000)
      (351863418470963 / 100000) := by
  exact
    packedTile65536 3518574848 3518705920 14 5970 59317 32 _ _ (2198131 / 100000) (1099067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518705920 :
    ThetaLowerSegment 3518705920 3518836992 (351863418470963 / 100000)
      (351876523745871 / 100000) := by
  exact
    packedTile65536 3518705920 3518836992 14 5962 59318 32 _ _ (1099067 / 50000) (2198137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518836992 :
    ThetaLowerSegment 3518836992 3518968064 (351876523745871 / 100000)
      (70377959220623 / 20000) := by
  exact
    packedTile65536 3518836992 3518968064 14 6038 59319 32 _ _ (1099069 / 50000) (2198141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3518968064 :
    ThetaLowerSegment 3518968064 3519099136 (70377959220623 / 20000)
      (351903053097517 / 100000) := by
  exact
    packedTile65536 3518968064 3519099136 14 6031 59320 32 _ _ (1099071 / 50000) (439629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519099136 :
    ThetaLowerSegment 3519099136 3519230208 (351903053097517 / 100000) (2815328142101 / 800) := by
  exact
    packedTile65536 3519099136 3519230208 14 5898 59321 32 _ _ (1099073 / 50000) (2198149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519230208 :
    ThetaLowerSegment 3519230208 3519361280 (2815328142101 / 800) (351928925293553 / 100000) := by
  exact
    packedTile65536 3519230208 3519361280 14 5872 59323 32 _ _ (2198149 / 100000) (274769 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519361280 :
    ThetaLowerSegment 3519361280 3519492352 (351928925293553 / 100000)
      (175970987863957 / 50000) := by
  exact
    packedTile65536 3519361280 3519492352 14 5937 59324 32 _ _ (2198153 / 100000) (549539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519492352 :
    ThetaLowerSegment 3519492352 3519623424 (175970987863957 / 50000)
      (351955078941791 / 100000) := by
  exact
    packedTile65536 3519492352 3519623424 14 5961 59325 32 _ _ (2198157 / 100000) (27477 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519623424 :
    ThetaLowerSegment 3519623424 3519754496 (351955078941791 / 100000)
      (351968287685231 / 100000) := by
  exact
    packedTile65536 3519623424 3519754496 14 6009 59326 32 _ _ (27477 / 1250) (2198163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519754496 :
    ThetaLowerSegment 3519754496 3519885568 (351968287685231 / 100000)
      (351981406327983 / 100000) := by
  exact
    packedTile65536 3519754496 3519885568 14 5968 59327 32 _ _ (549541 / 25000) (2198167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3519885568 :
    ThetaLowerSegment 3519885568 3520016640 (351981406327983 / 100000)
      (351994423878879 / 100000) := by
  exact
    packedTile65536 3519885568 3520016640 14 5922 59328 32 _ _ (274771 / 12500) (2198171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520016640 :
    ThetaLowerSegment 3520016640 3520147712 (351994423878879 / 100000)
      (352007450246151 / 100000) := by
  exact
    packedTile65536 3520016640 3520147712 14 5926 59329 32 _ _ (549543 / 25000) (87927 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520147712 :
    ThetaLowerSegment 3520147712 3520278784 (352007450246151 / 100000) (22001299710411 / 6250) := by
  exact
    packedTile65536 3520147712 3520278784 14 6071 59330 32 _ _ (87927 / 4000) (1099089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520278784 :
    ThetaLowerSegment 3520278784 3520409856 (22001299710411 / 6250) (352033850351657 / 100000) := by
  exact
    packedTile65536 3520278784 3520409856 14 5939 59331 32 _ _ (2198179 / 100000) (1099091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520409856 :
    ThetaLowerSegment 3520409856 3520540928 (352033850351657 / 100000)
      (352047039449657 / 100000) := by
  exact
    packedTile65536 3520409856 3520540928 14 6000 59333 32 _ _ (2198183 / 100000) (1099093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520540928 :
    ThetaLowerSegment 3520540928 3520672000 (352047039449657 / 100000) (22003767170849 / 6250) := by
  exact
    packedTile65536 3520540928 3520672000 14 6021 59334 32 _ _ (2198187 / 100000) (219819 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520672000 :
    ThetaLowerSegment 3520672000 3520803072 (22003767170849 / 6250) (44009177488723 / 12500) := by
  exact
    packedTile65536 3520672000 3520803072 14 5980 59335 32 _ _ (219819 / 10000) (2198193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520803072 :
    ThetaLowerSegment 3520803072 3520934144 (44009177488723 / 12500) (44010806350477 / 12500) := by
  exact
    packedTile65536 3520803072 3520934144 14 5928 59336 32 _ _ (1099097 / 50000) (2198197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3520934144 :
    ThetaLowerSegment 3520934144 3521065216 (44010806350477 / 12500) (176049766140057 / 50000) := by
  exact
    packedTile65536 3520934144 3521065216 14 5951 59337 32 _ _ (1099099 / 50000) (2198201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521065216 :
    ThetaLowerSegment 3521065216 3521196288 (176049766140057 / 50000) (70422535944059 / 20000) := by
  exact
    packedTile65536 3521065216 3521196288 14 5981 59338 32 _ _ (2198201 / 100000) (549551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521196288 :
    ThetaLowerSegment 3521196288 3521327360 (70422535944059 / 20000) (70425199289237 / 20000) := by
  exact
    packedTile65536 3521196288 3521327360 14 6058 59339 32 _ _ (439641 / 20000) (68694 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521327360 :
    ThetaLowerSegment 3521327360 3521458432 (70425199289237 / 20000)
      (352138974672121 / 100000) := by
  exact
    packedTile65536 3521327360 3521458432 14 5904 59340 32 _ _ (2198209 / 100000) (549553 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521458432 :
    ThetaLowerSegment 3521458432 3521589504 (352138974672121 / 100000) (4401901032703 / 1250) := by
  exact
    packedTile65536 3521458432 3521589504 14 5963 59341 32 _ _ (2198213 / 100000) (274777 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521589504 :
    ThetaLowerSegment 3521589504 3521720576 (4401901032703 / 1250) (11005158015221 / 3125) := by
  exact
    packedTile65536 3521589504 3521720576 14 5902 59342 32 _ _ (274777 / 12500) (2198219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521720576 :
    ThetaLowerSegment 3521720576 3521851648 (11005158015221 / 3125) (11005569631916 / 3125) := by
  exact
    packedTile65536 3521720576 3521851648 14 5992 59344 32 _ _ (109911 / 5000) (2198223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521851648 :
    ThetaLowerSegment 3521851648 3521982720 (11005569631916 / 3125) (22011942852093 / 6250) := by
  exact
    packedTile65536 3521851648 3521982720 14 5849 59345 32 _ _ (137389 / 6250) (2198227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3521982720 :
    ThetaLowerSegment 3521982720 3522113792 (22011942852093 / 6250) (352204193661089 / 100000) := by
  exact
    packedTile65536 3521982720 3522113792 14 5963 59346 32 _ _ (2198227 / 100000) (219823 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3522113792 :
    ThetaLowerSegment 3522113792 3522244864 (352204193661089 / 100000)
      (35221727533377 / 10000) := by
  exact
    packedTile65536 3522113792 3522244864 14 5951 59347 32 _ _ (2198231 / 100000) (1099117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3522244864 :
    ThetaLowerSegment 3522244864 3522375936 (35221727533377 / 10000) (8805758650977 / 2500) := by
  exact
    packedTile65536 3522244864 3522375936 14 5946 59348 32 _ _ (439647 / 20000) (1099119 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3522375936 :
    ThetaLowerSegment 3522375936 3522507008 (8805758650977 / 2500) (70448696103421 / 20000) := by
  exact
    packedTile65536 3522375936 3522507008 14 5975 59349 32 _ _ (2198239 / 100000) (1099121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3522507008 :
    ThetaLowerSegment 3522507008 3522638080 (70448696103421 / 20000)
      (352256601823603 / 100000) := by
  exact
    packedTile65536 3522507008 3522638080 14 5969 59350 32 _ _ (1099121 / 50000) (439649 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3522638080 :
    ThetaLowerSegment 3522638080 3522769152 (352256601823603 / 100000)
      (352269698973271 / 100000) := by
  exact
    packedTile65536 3522638080 3522769152 14 5958 59351 32 _ _ (1099123 / 50000) (2198249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3522769152 :
    ThetaLowerSegment 3522769152 3522900224 (352269698973271 / 100000)
      (352282886275021 / 100000) := by
  exact
    packedTile65536 3522769152 3522900224 14 5999 59352 32 _ _ (8793 / 400) (2198253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3522900224 :
    ThetaLowerSegment 3522900224 3523031296 (352282886275021 / 100000)
      (352295899938701 / 100000) := by
  exact
    packedTile65536 3522900224 3523031296 14 5920 59354 32 _ _ (1099127 / 50000) (2198257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523031296 :
    ThetaLowerSegment 3523031296 3523162368 (352295899938701 / 100000)
      (352309014739963 / 100000) := by
  exact
    packedTile65536 3523031296 3523162368 14 5966 59355 32 _ _ (2198257 / 100000) (109913 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523162368 :
    ThetaLowerSegment 3523162368 3523293440 (352309014739963 / 100000)
      (352322081203347 / 100000) := by
  exact
    packedTile65536 3523162368 3523293440 14 5944 59356 32 _ _ (2198261 / 100000) (274783 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523293440 :
    ThetaLowerSegment 3523293440 3523424512 (352322081203347 / 100000)
      (176167607918361 / 50000) := by
  exact
    packedTile65536 3523293440 3523424512 14 5975 59357 32 _ _ (439653 / 20000) (549567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523424512 :
    ThetaLowerSegment 3523424512 3523555584 (176167607918361 / 50000) (35234837466897 / 10000) := by
  exact
    packedTile65536 3523424512 3523555584 14 5986 59358 32 _ _ (549567 / 25000) (2198271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523555584 :
    ThetaLowerSegment 3523555584 3523686656 (35234837466897 / 10000) (176180709607509 / 50000) := by
  exact
    packedTile65536 3523555584 3523686656 14 5934 59359 32 _ _ (68696 / 3125) (87931 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523686656 :
    ThetaLowerSegment 3523686656 3523817728 (176180709607509 / 50000)
      (176187331913959 / 50000) := by
  exact
    packedTile65536 3523686656 3523817728 14 6025 59360 32 _ _ (549569 / 25000) (2198279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523817728 :
    ThetaLowerSegment 3523817728 3523948800 (176187331913959 / 50000)
      (176193880590079 / 50000) := by
  exact
    packedTile65536 3523817728 3523948800 14 5958 59361 32 _ _ (54957 / 2500) (2198283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3523948800 :
    ThetaLowerSegment 3523948800 3524079872 (176193880590079 / 50000)
      (352400988248969 / 100000) := by
  exact
    packedTile65536 3523948800 3524079872 14 6017 59362 32 _ _ (2198283 / 100000) (1099143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524079872 :
    ThetaLowerSegment 3524079872 3524210944 (352400988248969 / 100000)
      (70482803938861 / 20000) := by
  exact
    packedTile65536 3524079872 3524210944 14 5928 59363 32 _ _ (2198287 / 100000) (219829 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524210944 :
    ThetaLowerSegment 3524210944 3524342016 (70482803938861 / 20000)
      (352427002800951 / 100000) := by
  exact
    packedTile65536 3524210944 3524342016 14 5906 59365 32 _ _ (2198291 / 100000) (1099147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524342016 :
    ThetaLowerSegment 3524342016 3524473088 (352427002800951 / 100000)
      (352440273901829 / 100000) := by
  exact
    packedTile65536 3524342016 3524473088 14 6037 59366 32 _ _ (1099147 / 50000) (2198297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524473088 :
    ThetaLowerSegment 3524473088 3524604160 (352440273901829 / 100000)
      (352453265843009 / 100000) := by
  exact
    packedTile65536 3524473088 3524604160 14 5910 59367 32 _ _ (1099149 / 50000) (2198301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524604160 :
    ThetaLowerSegment 3524604160 3524735232 (352453265843009 / 100000)
      (70493266070359 / 20000) := by
  exact
    packedTile65536 3524604160 3524735232 14 5943 59368 32 _ _ (1099151 / 50000) (439661 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524735232 :
    ThetaLowerSegment 3524735232 3524866304 (70493266070359 / 20000)
      (352479548765773 / 100000) := by
  exact
    packedTile65536 3524735232 3524866304 14 6013 59369 32 _ _ (1099153 / 50000) (2198309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524866304 :
    ThetaLowerSegment 3524866304 3524997376 (352479548765773 / 100000)
      (88123181907057 / 25000) := by
  exact
    packedTile65536 3524866304 3524997376 14 5995 59370 32 _ _ (2198309 / 100000) (274789 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3524997376 :
    ThetaLowerSegment 3524997376 3525128448 (88123181907057 / 25000) (88126444203549 / 25000) := by
  exact
    packedTile65536 3524997376 3525128448 14 5936 59371 32 _ _ (2198313 / 100000) (549579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3525128448 :
    ThetaLowerSegment 3525128448 3525259520 (88126444203549 / 25000) (11016220732567 / 3125) := by
  exact
    packedTile65536 3525128448 3525259520 14 6044 59372 32 _ _ (2198317 / 100000) (27479 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3525259520 :
    ThetaLowerSegment 3525259520 3525390592 (11016220732567 / 3125) (11016631818407 / 3125) := by
  exact
    packedTile65536 3525259520 3525390592 14 5984 59373 32 _ _ (27479 / 1250) (2198323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3525390592 :
    ThetaLowerSegment 3525390592 3525521664 (11016631818407 / 3125) (8813632675253 / 2500) := by
  exact
    packedTile65536 3525390592 3525521664 14 5954 59374 32 _ _ (549581 / 25000) (2198327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3525521664 :
    ThetaLowerSegment 3525521664 3525652736 (8813632675253 / 2500) (11017450351354 / 3125) := by
  exact
    packedTile65536 3525521664 3525652736 14 5961 59376 32 _ _ (274791 / 12500) (2198331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3525652736 :
    ThetaLowerSegment 3525652736 3525783808 (11017450351354 / 3125) (44071426522347 / 12500) := by
  exact
    packedTile65536 3525652736 3525783808 14 5914 59377 32 _ _ (549583 / 25000) (439667 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3525783808 :
    ThetaLowerSegment 3525783808 3525914880 (44071426522347 / 12500)
      (352584621973791 / 100000) := by
  exact
    packedTile65536 3525783808 3525914880 14 6009 59378 32 _ _ (439667 / 20000) (1099169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3525914880 :
    ThetaLowerSegment 3525914880 3526045952 (352584621973791 / 100000)
      (176298880722997 / 50000) := by
  exact
    packedTile65536 3525914880 3526045952 14 5977 59379 32 _ _ (2198339 / 100000) (1099171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526045952 :
    ThetaLowerSegment 3526045952 3526177024 (176298880722997 / 50000)
      (176305396611649 / 50000) := by
  exact
    packedTile65536 3526045952 3526177024 14 5928 59380 32 _ _ (2198343 / 100000) (1099173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526177024 :
    ThetaLowerSegment 3526177024 3526308096 (176305396611649 / 50000)
      (176311938892321 / 50000) := by
  exact
    packedTile65536 3526177024 3526308096 14 5952 59381 32 _ _ (2198347 / 100000) (43967 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526308096 :
    ThetaLowerSegment 3526308096 3526439168 (176311938892321 / 50000)
      (176318551529121 / 50000) := by
  exact
    packedTile65536 3526308096 3526439168 14 6016 59382 32 _ _ (43967 / 2000) (2198353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526439168 :
    ThetaLowerSegment 3526439168 3526570240 (176318551529121 / 50000) (44081265488623 / 12500) := by
  exact
    packedTile65536 3526439168 3526570240 14 5923 59383 32 _ _ (1099177 / 50000) (2198357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526570240 :
    ThetaLowerSegment 3526570240 3526701312 (44081265488623 / 12500) (8816578015037 / 2500) := by
  exact
    packedTile65536 3526570240 3526701312 14 5912 59384 32 _ _ (1099179 / 50000) (2198361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526701312 :
    ThetaLowerSegment 3526701312 3526832384 (8816578015037 / 2500) (70535268748579 / 20000) := by
  exact
    packedTile65536 3526701312 3526832384 14 6015 59386 32 _ _ (2198361 / 100000) (549591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526832384 :
    ThetaLowerSegment 3526832384 3526963456 (70535268748579 / 20000) (14107580653839 / 4000) := by
  exact
    packedTile65536 3526832384 3526963456 14 5992 59387 32 _ _ (439673 / 20000) (68699 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3526963456 :
    ThetaLowerSegment 3526963456 3527094528 (14107580653839 / 4000) (176351365371017 / 50000) := by
  exact
    packedTile65536 3526963456 3527094528 14 6011 59388 32 _ _ (2198369 / 100000) (549593 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527094528 :
    ThetaLowerSegment 3527094528 3527225600 (176351365371017 / 50000) (35271577149067 / 10000) := by
  exact
    packedTile65536 3527094528 3527225600 14 5932 59389 32 _ _ (2198373 / 100000) (274797 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527225600 :
    ThetaLowerSegment 3527225600 3527356672 (35271577149067 / 10000) (176364483071711 / 50000) := by
  exact
    packedTile65536 3527225600 3527356672 14 6002 59390 32 _ _ (274797 / 12500) (2198379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527356672 :
    ThetaLowerSegment 3527356672 3527487744 (176364483071711 / 50000)
      (176371062823051 / 50000) := by
  exact
    packedTile65536 3527356672 3527487744 14 5986 59391 32 _ _ (109919 / 5000) (2198383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527487744 :
    ThetaLowerSegment 3527487744 3527618816 (176371062823051 / 50000)
      (176377639288787 / 50000) := by
  exact
    packedTile65536 3527487744 3527618816 14 5983 59392 32 _ _ (137399 / 6250) (2198387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527618816 :
    ThetaLowerSegment 3527618816 3527749888 (176377639288787 / 50000)
      (352768352385063 / 100000) := by
  exact
    packedTile65536 3527618816 3527749888 14 5947 59393 32 _ _ (2198387 / 100000) (219839 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527749888 :
    ThetaLowerSegment 3527749888 3527880960 (352768352385063 / 100000)
      (176390693322651 / 50000) := by
  exact
    packedTile65536 3527749888 3527880960 14 5929 59394 32 _ _ (2198391 / 100000) (1099197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3527880960 :
    ThetaLowerSegment 3527880960 3528012032 (176390693322651 / 50000)
      (176397275317281 / 50000) := by
  exact
    packedTile65536 3527880960 3528012032 14 5988 59395 32 _ _ (439679 / 20000) (1099199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528012032 :
    ThetaLowerSegment 3528012032 3528143104 (176397275317281 / 50000)
      (352807650894203 / 100000) := by
  exact
    packedTile65536 3528012032 3528143104 14 5959 59397 32 _ _ (2198399 / 100000) (1099201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528143104 :
    ThetaLowerSegment 3528143104 3528274176 (352807650894203 / 100000)
      (70564155510509 / 20000) := by
  exact
    packedTile65536 3528143104 3528274176 14 5971 59398 32 _ _ (1099201 / 50000) (439681 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528274176 :
    ThetaLowerSegment 3528274176 3528405248 (70564155510509 / 20000)
      (352833893242741 / 100000) := by
  exact
    packedTile65536 3528274176 3528405248 14 5966 59399 32 _ _ (1099203 / 50000) (2198409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528405248 :
    ThetaLowerSegment 3528405248 3528536320 (352833893242741 / 100000)
      (352846883647431 / 100000) := by
  exact
    packedTile65536 3528405248 3528536320 14 5909 59400 32 _ _ (219841 / 10000) (2198413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528536320 :
    ThetaLowerSegment 3528536320 3528667392 (352846883647431 / 100000)
      (352859977395259 / 100000) := by
  exact
    packedTile65536 3528536320 3528667392 14 5956 59401 32 _ _ (2198413 / 100000) (137401 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528667392 :
    ThetaLowerSegment 3528667392 3528798464 (352859977395259 / 100000)
      (352873154706757 / 100000) := by
  exact
    packedTile65536 3528667392 3528798464 14 5994 59402 32 _ _ (2198417 / 100000) (109921 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528798464 :
    ThetaLowerSegment 3528798464 3528929536 (352873154706757 / 100000)
      (35288628587539 / 10000) := by
  exact
    packedTile65536 3528798464 3528929536 14 5973 59403 32 _ _ (2198421 / 100000) (274803 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3528929536 :
    ThetaLowerSegment 3528929536 3529060608 (35288628587539 / 10000) (4411240432483 / 1250) := by
  exact
    packedTile65536 3528929536 3529060608 14 5890 59404 32 _ _ (87937 / 4000) (549607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529060608 :
    ThetaLowerSegment 3529060608 3529191680 (4411240432483 / 1250) (88228104642839 / 25000) := by
  exact
    packedTile65536 3529060608 3529191680 14 5997 59405 32 _ _ (549607 / 25000) (2198431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529191680 :
    ThetaLowerSegment 3529191680 3529322752 (88228104642839 / 25000) (3529253717327 / 1000) := by
  exact
    packedTile65536 3529191680 3529322752 14 5892 59407 32 _ _ (68701 / 3125) (439687 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529322752 :
    ThetaLowerSegment 3529322752 3529339136 (3529253717327 / 1000) (44115871249459 / 12500) := by
  exact
    packedTile65536 3529322752 3529339136 11 727 59408 32 _ _ (549609 / 25000) (2198439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3529339136 :
    ThetaLowerSegment 3529339136 3529341184 (44115871249459 / 12500) (88231801307081 / 25000) := by
  exact
    packedTile65536 3529339136 3529341184 8 107 59408 32 _ _ (549609 / 25000) (2198439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3497341184_3529341184 :
    ThetaLowerSegment 3497341184 3529341184 (349726131531189 / 100000)
      (88231801307081 / 25000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3497341184 cell3497472256)
                  (ThetaLowerSegment.join cell3497603328 cell3497734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3497865472 cell3497996544)
                  (ThetaLowerSegment.join cell3498127616 cell3498258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3498389760 cell3498520832)
                  (ThetaLowerSegment.join cell3498651904 cell3498782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3498914048 cell3499045120)
                  (ThetaLowerSegment.join cell3499176192 cell3499307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3499438336 cell3499569408)
                  (ThetaLowerSegment.join cell3499700480 cell3499831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3499962624 cell3500093696)
                  (ThetaLowerSegment.join cell3500224768 cell3500355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3500486912 cell3500617984)
                  (ThetaLowerSegment.join cell3500749056 cell3500880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3501011200 cell3501142272)
                  (ThetaLowerSegment.join cell3501273344 cell3501404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3501535488 cell3501666560)
                  (ThetaLowerSegment.join cell3501797632 cell3501928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3502059776 cell3502190848)
                  (ThetaLowerSegment.join cell3502321920 cell3502452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3502584064 cell3502715136)
                  (ThetaLowerSegment.join cell3502846208 cell3502977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3503108352 cell3503239424)
                  (ThetaLowerSegment.join cell3503370496 cell3503501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3503632640 cell3503763712)
                  (ThetaLowerSegment.join cell3503894784 cell3504025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3504156928 cell3504288000)
                  (ThetaLowerSegment.join cell3504419072 cell3504550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3504681216 cell3504812288)
                  (ThetaLowerSegment.join cell3504943360 cell3505074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3505205504 cell3505336576)
                  (ThetaLowerSegment.join cell3505467648 cell3505598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3505729792 cell3505860864)
                  (ThetaLowerSegment.join cell3505991936 cell3506123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3506254080 cell3506385152)
                  (ThetaLowerSegment.join cell3506516224 cell3506647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3506778368 cell3506909440)
                  (ThetaLowerSegment.join cell3507040512 cell3507171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3507302656 cell3507433728)
                  (ThetaLowerSegment.join cell3507564800 cell3507695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3507826944 cell3507958016)
                  (ThetaLowerSegment.join cell3508089088 cell3508220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3508351232 cell3508482304)
                  (ThetaLowerSegment.join cell3508613376 cell3508744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3508875520 cell3509006592)
                  (ThetaLowerSegment.join cell3509137664 cell3509268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3509399808 cell3509530880)
                  (ThetaLowerSegment.join cell3509661952 cell3509793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3509924096 cell3510055168)
                  (ThetaLowerSegment.join cell3510186240 cell3510317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3510448384 cell3510579456)
                  (ThetaLowerSegment.join cell3510710528 cell3510841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3510972672 cell3511103744)
                  (ThetaLowerSegment.join cell3511234816 cell3511365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3511496960 cell3511628032)
                  (ThetaLowerSegment.join cell3511759104 cell3511890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3512021248 cell3512152320)
                  (ThetaLowerSegment.join cell3512283392 cell3512414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3512545536 cell3512676608)
                  (ThetaLowerSegment.join cell3512807680 cell3512938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3513069824 cell3513200896)
                  (ThetaLowerSegment.join cell3513331968 cell3513463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3513594112 cell3513725184)
                  (ThetaLowerSegment.join cell3513856256 cell3513987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3514118400 cell3514249472)
                  (ThetaLowerSegment.join cell3514380544 cell3514511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3514642688 cell3514773760)
                  (ThetaLowerSegment.join cell3514904832 cell3515035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3515166976 cell3515298048)
                  (ThetaLowerSegment.join cell3515429120 cell3515560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3515691264 cell3515822336)
                  (ThetaLowerSegment.join cell3515953408 cell3516084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3516215552 cell3516346624)
                  (ThetaLowerSegment.join cell3516477696 cell3516608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3516739840 cell3516870912)
                  (ThetaLowerSegment.join cell3517001984 cell3517133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3517264128 cell3517395200)
                  (ThetaLowerSegment.join cell3517526272 cell3517657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3517788416 cell3517919488)
                  (ThetaLowerSegment.join cell3518050560 cell3518181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3518312704 cell3518443776)
                  (ThetaLowerSegment.join cell3518574848 cell3518705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3518836992 cell3518968064)
                  (ThetaLowerSegment.join cell3519099136 cell3519230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3519361280 cell3519492352)
                  (ThetaLowerSegment.join cell3519623424 cell3519754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3519885568 cell3520016640)
                  (ThetaLowerSegment.join cell3520147712 cell3520278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3520409856 cell3520540928)
                  (ThetaLowerSegment.join cell3520672000 cell3520803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3520934144 cell3521065216)
                  (ThetaLowerSegment.join cell3521196288 cell3521327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3521458432 cell3521589504)
                  (ThetaLowerSegment.join cell3521720576 cell3521851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3521982720 cell3522113792)
                  (ThetaLowerSegment.join cell3522244864 cell3522375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3522507008 cell3522638080)
                  (ThetaLowerSegment.join cell3522769152 cell3522900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3523031296 cell3523162368)
                  (ThetaLowerSegment.join cell3523293440 cell3523424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3523555584 cell3523686656)
                  (ThetaLowerSegment.join cell3523817728 cell3523948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3524079872 cell3524210944)
                  (ThetaLowerSegment.join cell3524342016 cell3524473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3524604160 cell3524735232)
                  (ThetaLowerSegment.join cell3524866304 cell3524997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3525128448 cell3525259520)
                  (ThetaLowerSegment.join cell3525390592 cell3525521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3525652736 cell3525783808)
                  (ThetaLowerSegment.join cell3525914880 cell3526045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3526177024 cell3526308096)
                  (ThetaLowerSegment.join cell3526439168 cell3526570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3526701312 cell3526832384)
                  (ThetaLowerSegment.join cell3526963456 cell3527094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3527225600 cell3527356672)
                  (ThetaLowerSegment.join cell3527487744 cell3527618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3527749888 cell3527880960)
                  (ThetaLowerSegment.join cell3528012032 cell3528143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3528274176 cell3528405248)
                  (ThetaLowerSegment.join cell3528536320 cell3528667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3528798464 cell3528929536)
                (ThetaLowerSegment.join cell3529060608 cell3529191680))
              (ThetaLowerSegment.join cell3529322752 cell3529339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
