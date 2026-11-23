/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis8192

/-! # Direct theta estimate up to 42488064 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell31072512 :
    ThetaLowerSegment 31072512 31088896 (3106694022169 / 100000) (3108310517703 / 100000) := by
  exact
    packedTile8192 31072512 31088896 11 937 5574 25 _ _ (862591 / 50000) (345037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31088896 :
    ThetaLowerSegment 31088896 31105280 (3108310517703 / 100000) (777474002167 / 25000) := by
  exact
    packedTile8192 31088896 31105280 11 919 5575 25 _ _ (345047 / 20000) (862619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31105280 :
    ThetaLowerSegment 31105280 31121664 (777474002167 / 25000) (777891521621 / 25000) := by
  exact
    packedTile8192 31105280 31121664 11 968 5577 25 _ _ (1725287 / 100000) (172529 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31121664 :
    ThetaLowerSegment 31121664 31138048 (777891521621 / 25000) (97288901322 / 3125) := by
  exact
    packedTile8192 31121664 31138048 11 973 5578 25 _ _ (86267 / 5000) (1725343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31138048 :
    ThetaLowerSegment 31138048 31154432 (97288901322 / 3125) (3114882240261 / 100000) := by
  exact
    packedTile8192 31138048 31154432 11 949 5580 25 _ _ (1725393 / 100000) (431349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31154432 :
    ThetaLowerSegment 31154432 31170816 (3114882240261 / 100000) (3116493805891 / 100000) := by
  exact
    packedTile8192 31154432 31170816 11 934 5581 25 _ _ (345089 / 20000) (215681 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31170816 :
    ThetaLowerSegment 31170816 31187200 (3116493805891 / 100000) (3118088166043 / 100000) := by
  exact
    packedTile8192 31170816 31187200 11 924 5583 25 _ _ (862749 / 50000) (1725501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31187200 :
    ThetaLowerSegment 31187200 31203584 (3118088166043 / 100000) (3119742968493 / 100000) := by
  exact
    packedTile8192 31187200 31203584 11 959 5584 25 _ _ (34511 / 2000) (1725553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31203584 :
    ThetaLowerSegment 31203584 31219968 (3119742968493 / 100000) (312136330971 / 10000) := by
  exact
    packedTile8192 31203584 31219968 11 939 5586 25 _ _ (1725603 / 100000) (862803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31219968 :
    ThetaLowerSegment 31219968 31236352 (312136330971 / 10000) (156151169491 / 5000) := by
  exact
    packedTile8192 31219968 31236352 11 962 5587 25 _ _ (345131 / 20000) (862829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31236352 :
    ThetaLowerSegment 31236352 31252736 (156151169491 / 5000) (781157937419 / 25000) := by
  exact
    packedTile8192 31236352 31252736 11 932 5588 25 _ _ (431427 / 25000) (1725711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31252736 :
    ThetaLowerSegment 31252736 31269120 (781157937419 / 25000) (781563922459 / 25000) := by
  exact
    packedTile8192 31252736 31269120 11 941 5590 25 _ _ (10786 / 625) (1725763 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31269120 :
    ThetaLowerSegment 31269120 31285504 (781563922459 / 25000) (3127962518893 / 100000) := by
  exact
    packedTile8192 31269120 31285504 11 989 5591 25 _ _ (1725813 / 100000) (215727 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31285504 :
    ThetaLowerSegment 31285504 31301888 (3127962518893 / 100000) (1564793278929 / 50000) := by
  exact
    packedTile8192 31285504 31301888 11 941 5593 25 _ _ (345173 / 20000) (431467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31301888 :
    ThetaLowerSegment 31301888 31318272 (1564793278929 / 50000) (1565638978259 / 50000) := by
  exact
    packedTile8192 31301888 31318272 11 980 5594 25 _ _ (1725917 / 100000) (10787 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31318272 :
    ThetaLowerSegment 31318272 31334656 (1565638978259 / 50000) (783222934617 / 25000) := by
  exact
    packedTile8192 31318272 31334656 11 935 5596 25 _ _ (172597 / 10000) (1725973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31334656 :
    ThetaLowerSegment 31334656 31351040 (783222934617 / 25000) (1567264866673 / 50000) := by
  exact
    packedTile8192 31334656 31351040 11 949 5597 25 _ _ (863011 / 50000) (69041 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31351040 :
    ThetaLowerSegment 31351040 31367424 (1567264866673 / 50000) (392019677641 / 12500) := by
  exact
    packedTile8192 31351040 31367424 11 943 5599 25 _ _ (863037 / 50000) (1726077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31367424 :
    ThetaLowerSegment 31367424 31383808 (392019677641 / 12500) (627556341327 / 20000) := by
  exact
    packedTile8192 31367424 31383808 11 941 5600 25 _ _ (1726127 / 100000) (172613 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31383808 :
    ThetaLowerSegment 31383808 31400192 (627556341327 / 20000) (313941294579 / 10000) := by
  exact
    packedTile8192 31383808 31400192 11 945 5602 25 _ _ (1726179 / 100000) (863091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31400192 :
    ThetaLowerSegment 31400192 31416576 (313941294579 / 10000) (1570528158851 / 50000) := by
  exact
    packedTile8192 31400192 31416576 11 952 5603 25 _ _ (1726231 / 100000) (863117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31416576 :
    ThetaLowerSegment 31416576 31432960 (1570528158851 / 50000) (785668892789 / 25000) := by
  exact
    packedTile8192 31416576 31432960 11 938 5605 25 _ _ (1726283 / 100000) (863143 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31432960 :
    ThetaLowerSegment 31432960 31449344 (785668892789 / 25000) (3144306957731 / 100000) := by
  exact
    packedTile8192 31432960 31449344 11 945 5606 25 _ _ (345267 / 20000) (863169 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31449344 :
    ThetaLowerSegment 31449344 31465728 (3144306957731 / 100000) (3145922855963 / 100000) := by
  exact
    packedTile8192 31449344 31465728 11 936 5607 25 _ _ (1726387 / 100000) (172639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31465728 :
    ThetaLowerSegment 31465728 31482112 (3145922855963 / 100000) (3147531897111 / 100000) := by
  exact
    packedTile8192 31465728 31482112 11 932 5609 25 _ _ (1726439 / 100000) (863221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31482112 :
    ThetaLowerSegment 31482112 31498496 (3147531897111 / 100000) (3149156526083 / 100000) := by
  exact
    packedTile8192 31482112 31498496 11 941 5610 25 _ _ (431623 / 25000) (345299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31498496 :
    ThetaLowerSegment 31498496 31514880 (3149156526083 / 100000) (3150755305827 / 100000) := by
  exact
    packedTile8192 31498496 31514880 11 926 5612 25 _ _ (107909 / 6250) (1726547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31514880 :
    ThetaLowerSegment 31514880 31531264 (3150755305827 / 100000) (3152390392239 / 100000) := by
  exact
    packedTile8192 31514880 31531264 11 947 5613 25 _ _ (431649 / 25000) (1726599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31531264 :
    ThetaLowerSegment 31531264 31547648 (3152390392239 / 100000) (3153997901527 / 100000) := by
  exact
    packedTile8192 31531264 31547648 11 931 5615 25 _ _ (215831 / 12500) (1726651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31547648 :
    ThetaLowerSegment 31547648 31564032 (3153997901527 / 100000) (3155690066547 / 100000) := by
  exact
    packedTile8192 31547648 31564032 11 980 5616 25 _ _ (1726699 / 100000) (863351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31564032 :
    ThetaLowerSegment 31564032 31580416 (3155690066547 / 100000) (126295153161 / 4000) := by
  exact
    packedTile8192 31564032 31580416 11 978 5618 25 _ _ (1726751 / 100000) (863377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31580416 :
    ThetaLowerSegment 31580416 31596800 (126295153161 / 4000) (1579507055733 / 50000) := by
  exact
    packedTile8192 31580416 31596800 11 947 5619 25 _ _ (1726803 / 100000) (863403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31596800 :
    ThetaLowerSegment 31596800 31613184 (1579507055733 / 50000) (3160621813471 / 100000) := by
  exact
    packedTile8192 31596800 31613184 11 931 5621 25 _ _ (345371 / 20000) (863429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31613184 :
    ThetaLowerSegment 31613184 31629568 (3160621813471 / 100000) (790569479321 / 25000) := by
  exact
    packedTile8192 31613184 31629568 11 959 5622 25 _ _ (1726907 / 100000) (172691 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31629568 :
    ThetaLowerSegment 31629568 31645952 (790569479321 / 25000) (3163913347457 / 100000) := by
  exact
    packedTile8192 31629568 31645952 11 947 5624 25 _ _ (1726959 / 100000) (863481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31645952 :
    ThetaLowerSegment 31645952 31662336 (3163913347457 / 100000) (791386343213 / 25000) := by
  exact
    packedTile8192 31645952 31662336 11 945 5625 25 _ _ (1727011 / 100000) (863507 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31662336 :
    ThetaLowerSegment 31662336 31678720 (791386343213 / 25000) (395905168467 / 12500) := by
  exact
    packedTile8192 31662336 31678720 11 982 5626 25 _ _ (863531 / 50000) (345413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31678720 :
    ThetaLowerSegment 31678720 31695104 (395905168467 / 12500) (792217072281 / 25000) := by
  exact
    packedTile8192 31678720 31695104 11 942 5628 25 _ _ (863557 / 50000) (1727117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31695104 :
    ThetaLowerSegment 31695104 31711488 (792217072281 / 25000) (1585251957663 / 50000) := by
  exact
    packedTile8192 31695104 31711488 11 947 5629 25 _ _ (863583 / 50000) (1727169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31711488 :
    ThetaLowerSegment 31711488 31727872 (1585251957663 / 50000) (3172080864447 / 100000) := by
  exact
    packedTile8192 31711488 31727872 11 913 5631 25 _ _ (1727217 / 100000) (86361 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31727872 :
    ThetaLowerSegment 31727872 31744256 (3172080864447 / 100000) (1586861748633 / 50000) := by
  exact
    packedTile8192 31727872 31744256 11 951 5632 25 _ _ (1727269 / 100000) (215909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31744256 :
    ThetaLowerSegment 31744256 31760640 (1586861748633 / 50000) (635062181053 / 20000) := by
  exact
    packedTile8192 31744256 31760640 11 919 5634 25 _ _ (1727321 / 100000) (431831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31760640 :
    ThetaLowerSegment 31760640 31777024 (635062181053 / 20000) (3176993365593 / 100000) := by
  exact
    packedTile8192 31760640 31777024 11 974 5635 25 _ _ (431843 / 25000) (13819 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31777024 :
    ThetaLowerSegment 31777024 31793408 (3176993365593 / 100000) (3178624053849 / 100000) := by
  exact
    packedTile8192 31777024 31793408 11 944 5637 25 _ _ (53982 / 3125) (1727427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31793408 :
    ThetaLowerSegment 31793408 31809792 (3178624053849 / 100000) (3180278974899 / 100000) := by
  exact
    packedTile8192 31793408 31809792 11 958 5638 25 _ _ (69099 / 4000) (863739 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31809792 :
    ThetaLowerSegment 31809792 31826176 (3180278974899 / 100000) (1590969564173 / 50000) := by
  exact
    packedTile8192 31809792 31826176 11 961 5640 25 _ _ (1727527 / 100000) (172753 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31826176 :
    ThetaLowerSegment 31826176 31842560 (1590969564173 / 50000) (397946893089 / 12500) := by
  exact
    packedTile8192 31826176 31842560 11 947 5641 25 _ _ (863789 / 50000) (1727581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31842560 :
    ThetaLowerSegment 31842560 31858944 (397946893089 / 12500) (1592633247241 / 50000) := by
  exact
    packedTile8192 31842560 31858944 11 979 5642 25 _ _ (172763 / 10000) (1727633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31858944 :
    ThetaLowerSegment 31858944 31875328 (1592633247241 / 50000) (1593448712673 / 50000) := by
  exact
    packedTile8192 31858944 31875328 11 944 5644 25 _ _ (1727681 / 100000) (431921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31875328 :
    ThetaLowerSegment 31875328 31891712 (1593448712673 / 50000) (398565618729 / 12500) := by
  exact
    packedTile8192 31875328 31891712 11 942 5645 25 _ _ (1727733 / 100000) (215967 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31891712 :
    ThetaLowerSegment 31891712 31908096 (398565618729 / 12500) (199384856607 / 6250) := by
  exact
    packedTile8192 31891712 31908096 11 945 5647 25 _ _ (215973 / 12500) (1727787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31908096 :
    ThetaLowerSegment 31908096 31924480 (199384856607 / 6250) (159591080589 / 5000) := by
  exact
    packedTile8192 31908096 31924480 11 963 5648 25 _ _ (431959 / 25000) (1727839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31924480 :
    ThetaLowerSegment 31924480 31940864 (159591080589 / 5000) (3193423363029 / 100000) := by
  exact
    packedTile8192 31924480 31940864 11 927 5650 25 _ _ (1727887 / 100000) (172789 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31940864 :
    ThetaLowerSegment 31940864 31957248 (3193423363029 / 100000) (3195064904129 / 100000) := by
  exact
    packedTile8192 31940864 31957248 11 950 5651 25 _ _ (863969 / 50000) (1727941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31957248 :
    ThetaLowerSegment 31957248 31973632 (3195064904129 / 100000) (3196720317591 / 100000) := by
  exact
    packedTile8192 31957248 31973632 11 958 5653 25 _ _ (1727989 / 100000) (215999 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31973632 :
    ThetaLowerSegment 31973632 31990016 (3196720317591 / 100000) (399792436501 / 12500) := by
  exact
    packedTile8192 31973632 31990016 11 937 5654 25 _ _ (1728041 / 100000) (432011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell31990016 :
    ThetaLowerSegment 31990016 32006400 (399792436501 / 12500) (79999788699 / 2500) := by
  exact
    packedTile8192 31990016 32006400 11 956 5655 25 _ _ (432023 / 25000) (345619 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32006400 :
    ThetaLowerSegment 32006400 32022784 (79999788699 / 2500) (1600806273047 / 50000) := by
  exact
    packedTile8192 32006400 32022784 11 938 5657 25 _ _ (1728143 / 100000) (864073 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32022784 :
    ThetaLowerSegment 32022784 32039168 (1600806273047 / 50000) (800803645483 / 25000) := by
  exact
    packedTile8192 32022784 32039168 11 927 5658 25 _ _ (864097 / 50000) (1728197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32039168 :
    ThetaLowerSegment 32039168 32055552 (800803645483 / 25000) (801211511303 / 25000) := by
  exact
    packedTile8192 32039168 32055552 11 944 5660 25 _ _ (345649 / 20000) (216031 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32055552 :
    ThetaLowerSegment 32055552 32071936 (801211511303 / 25000) (3206489655659 / 100000) := by
  exact
    packedTile8192 32055552 32071936 11 951 5661 25 _ _ (1728297 / 100000) (17283 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32071936 :
    ThetaLowerSegment 32071936 32088320 (3206489655659 / 100000) (3208150598087 / 100000) := by
  exact
    packedTile8192 32071936 32088320 11 961 5663 25 _ _ (432087 / 25000) (1728351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32088320 :
    ThetaLowerSegment 32088320 32104704 (3208150598087 / 100000) (641955749989 / 20000) := by
  exact
    packedTile8192 32088320 32104704 11 942 5664 25 _ _ (1728399 / 100000) (864201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32104704 :
    ThetaLowerSegment 32104704 32121088 (641955749989 / 20000) (642298674469 / 20000) := by
  exact
    packedTile8192 32104704 32121088 11 992 5666 25 _ _ (34569 / 2000) (1728453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32121088 :
    ThetaLowerSegment 32121088 32137472 (642298674469 / 20000) (1606542660883 / 50000) := by
  exact
    packedTile8192 32121088 32137472 11 921 5667 25 _ _ (1728501 / 100000) (216063 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32137472 :
    ThetaLowerSegment 32137472 32153856 (1606542660883 / 50000) (321477411707 / 10000) := by
  exact
    packedTile8192 32137472 32153856 11 977 5668 25 _ _ (216069 / 12500) (345711 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32153856 :
    ThetaLowerSegment 32153856 32170240 (321477411707 / 10000) (3216400732493 / 100000) := by
  exact
    packedTile8192 32153856 32170240 11 941 5670 25 _ _ (1728603 / 100000) (864303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32170240 :
    ThetaLowerSegment 32170240 32186624 (3216400732493 / 100000) (3218023938599 / 100000) := by
  exact
    packedTile8192 32170240 32186624 11 939 5671 25 _ _ (864327 / 50000) (1728657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32186624 :
    ThetaLowerSegment 32186624 32203008 (3218023938599 / 100000) (3219638549069 / 100000) := by
  exact
    packedTile8192 32186624 32203008 11 934 5673 25 _ _ (345741 / 20000) (432177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32203008 :
    ThetaLowerSegment 32203008 32219392 (3219638549069 / 100000) (644249604181 / 20000) := by
  exact
    packedTile8192 32203008 32219392 11 931 5674 25 _ _ (432189 / 25000) (1728759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32219392 :
    ThetaLowerSegment 32219392 32235776 (644249604181 / 20000) (128913540897 / 4000) := by
  exact
    packedTile8192 32219392 32235776 11 920 5676 25 _ _ (864403 / 50000) (1728809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32235776 :
    ThetaLowerSegment 32235776 32252160 (128913540897 / 4000) (3224522429143 / 100000) := by
  exact
    packedTile8192 32235776 32252160 11 974 5677 25 _ _ (1728857 / 100000) (86443 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32252160 :
    ThetaLowerSegment 32252160 32268544 (3224522429143 / 100000) (3226151060479 / 100000) := by
  exact
    packedTile8192 32252160 32268544 11 942 5679 25 _ _ (432227 / 25000) (1728911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32268544 :
    ThetaLowerSegment 32268544 32284928 (3226151060479 / 100000) (322779184257 / 10000) := by
  exact
    packedTile8192 32268544 32284928 11 949 5680 25 _ _ (1728959 / 100000) (864481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32284928 :
    ThetaLowerSegment 32284928 32301312 (322779184257 / 10000) (16147457297 / 500) := by
  exact
    packedTile8192 32284928 32301312 11 983 5681 25 _ _ (172901 / 10000) (1729013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32301312 :
    ThetaLowerSegment 32301312 32317696 (16147457297 / 500) (40388916471 / 1250) := by
  exact
    packedTile8192 32301312 32317696 11 938 5683 25 _ _ (86453 / 5000) (1729063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32317696 :
    ThetaLowerSegment 32317696 32334080 (40388916471 / 1250) (161636934101 / 5000) := by
  exact
    packedTile8192 32317696 32334080 11 940 5684 25 _ _ (1729111 / 100000) (864557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32334080 :
    ThetaLowerSegment 32334080 32350464 (161636934101 / 5000) (1617198474189 / 50000) := by
  exact
    packedTile8192 32334080 32350464 11 959 5686 25 _ _ (864581 / 50000) (345833 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32350464 :
    ThetaLowerSegment 32350464 32366848 (1617198474189 / 50000) (1618023308313 / 50000) := by
  exact
    packedTile8192 32350464 32366848 11 954 5687 25 _ _ (432303 / 25000) (345843 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32366848 :
    ThetaLowerSegment 32366848 32383232 (1618023308313 / 50000) (1618822227819 / 50000) := by
  exact
    packedTile8192 32366848 32383232 11 924 5689 25 _ _ (1729263 / 100000) (864633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32383232 :
    ThetaLowerSegment 32383232 32399616 (1618822227819 / 50000) (404916749427 / 12500) := by
  exact
    packedTile8192 32383232 32399616 11 977 5690 25 _ _ (864657 / 50000) (1729317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32399616 :
    ThetaLowerSegment 32399616 32416000 (404916749427 / 12500) (101279446998 / 3125) := by
  exact
    packedTile8192 32399616 32416000 11 930 5692 25 _ _ (432341 / 25000) (1729367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32416000 :
    ThetaLowerSegment 32416000 32432384 (101279446998 / 3125) (3242593895261 / 100000) := by
  exact
    packedTile8192 32416000 32432384 11 955 5693 25 _ _ (345883 / 20000) (864709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32432384 :
    ThetaLowerSegment 32432384 32448768 (3242593895261 / 100000) (405525503397 / 12500) := by
  exact
    packedTile8192 32432384 32448768 11 931 5694 25 _ _ (345893 / 20000) (432367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32448768 :
    ThetaLowerSegment 32448768 32465152 (405525503397 / 12500) (405733045317 / 12500) := by
  exact
    packedTile8192 32448768 32465152 11 960 5696 25 _ _ (432379 / 25000) (1729519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32465152 :
    ThetaLowerSegment 32465152 32481536 (405733045317 / 12500) (1623777074259 / 50000) := by
  exact
    packedTile8192 32465152 32481536 11 977 5697 25 _ _ (864783 / 50000) (1729569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32481536 :
    ThetaLowerSegment 32481536 32497920 (1623777074259 / 50000) (1624600371951 / 50000) := by
  exact
    packedTile8192 32481536 32497920 11 952 5699 25 _ _ (1729617 / 100000) (86481 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32497920 :
    ThetaLowerSegment 32497920 32514304 (1624600371951 / 50000) (812705792887 / 25000) := by
  exact
    packedTile8192 32497920 32514304 11 938 5700 25 _ _ (1729667 / 100000) (172967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32514304 :
    ThetaLowerSegment 32514304 32530688 (812705792887 / 25000) (203278285369 / 6250) := by
  exact
    packedTile8192 32514304 32530688 11 942 5702 25 _ _ (864859 / 50000) (1729721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32530688 :
    ThetaLowerSegment 32530688 32547072 (203278285369 / 6250) (101690927614 / 3125) := by
  exact
    packedTile8192 32530688 32547072 11 958 5703 25 _ _ (216221 / 12500) (1729771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32547072 :
    ThetaLowerSegment 32547072 32563456 (101690927614 / 3125) (406966964071 / 12500) := by
  exact
    packedTile8192 32547072 32563456 11 940 5705 25 _ _ (864909 / 50000) (1729821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32563456 :
    ThetaLowerSegment 32563456 32579840 (406966964071 / 12500) (814347366833 / 25000) := by
  exact
    packedTile8192 32563456 32579840 11 956 5706 25 _ _ (1729869 / 100000) (108117 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32579840 :
    ThetaLowerSegment 32579840 32596224 (814347366833 / 25000) (3259083058033 / 100000) := by
  exact
    packedTile8192 32579840 32596224 11 979 5707 25 _ _ (1729919 / 100000) (864961 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32596224 :
    ThetaLowerSegment 32596224 32612608 (3259083058033 / 100000) (1630352019493 / 50000) := by
  exact
    packedTile8192 32596224 32612608 11 937 5709 25 _ _ (1729969 / 100000) (432493 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32612608 :
    ThetaLowerSegment 32612608 32628992 (1630352019493 / 50000) (3262359667169 / 100000) := by
  exact
    packedTile8192 32612608 32628992 11 957 5710 25 _ _ (1730019 / 100000) (865011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32628992 :
    ThetaLowerSegment 32628992 32645376 (3262359667169 / 100000) (3263970362339 / 100000) := by
  exact
    packedTile8192 32628992 32645376 11 931 5712 25 _ _ (173007 / 10000) (1730073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32645376 :
    ThetaLowerSegment 32645376 32661760 (3263970362339 / 100000) (3265560342619 / 100000) := by
  exact
    packedTile8192 32645376 32661760 11 919 5713 25 _ _ (43253 / 2500) (1730123 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32661760 :
    ThetaLowerSegment 32661760 32678144 (3265560342619 / 100000) (3267235147179 / 100000) := by
  exact
    packedTile8192 32661760 32678144 11 968 5715 25 _ _ (173017 / 10000) (1730173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32678144 :
    ThetaLowerSegment 32678144 32694528 (3267235147179 / 100000) (3268887507279 / 100000) := by
  exact
    packedTile8192 32678144 32694528 11 955 5716 25 _ _ (86511 / 5000) (1730223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32694528 :
    ThetaLowerSegment 32694528 32710912 (3268887507279 / 100000) (3270510500539 / 100000) := by
  exact
    packedTile8192 32694528 32710912 11 938 5717 25 _ _ (173027 / 10000) (1730273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32710912 :
    ThetaLowerSegment 32710912 32727296 (3270510500539 / 100000) (3272162956139 / 100000) := by
  exact
    packedTile8192 32710912 32727296 11 955 5719 25 _ _ (21629 / 1250) (1730323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32727296 :
    ThetaLowerSegment 32727296 32743680 (3272162956139 / 100000) (3273792965621 / 100000) := by
  exact
    packedTile8192 32727296 32743680 11 942 5720 25 _ _ (1730371 / 100000) (865187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32743680 :
    ThetaLowerSegment 32743680 32760064 (3273792965621 / 100000) (1637703724207 / 50000) := by
  exact
    packedTile8192 32743680 32760064 11 933 5722 25 _ _ (1730421 / 100000) (216303 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32760064 :
    ThetaLowerSegment 32760064 32776448 (1637703724207 / 50000) (819257657553 / 25000) := by
  exact
    packedTile8192 32760064 32776448 11 938 5723 25 _ _ (1730471 / 100000) (865237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32776448 :
    ThetaLowerSegment 32776448 32792832 (819257657553 / 25000) (3278693660893 / 100000) := by
  exact
    packedTile8192 32776448 32792832 11 961 5725 25 _ _ (1730521 / 100000) (432631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32792832 :
    ThetaLowerSegment 32792832 32809216 (3278693660893 / 100000) (410041131311 / 12500) := by
  exact
    packedTile8192 32792832 32809216 11 945 5726 25 _ _ (1730571 / 100000) (865287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32809216 :
    ThetaLowerSegment 32809216 32825600 (410041131311 / 12500) (3281922952429 / 100000) := by
  exact
    packedTile8192 32809216 32825600 11 921 5727 25 _ _ (1730621 / 100000) (54082 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32825600 :
    ThetaLowerSegment 32825600 32841984 (3281922952429 / 100000) (3283565358259 / 100000) := by
  exact
    packedTile8192 32825600 32841984 11 949 5729 25 _ _ (173067 / 10000) (1730673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32841984 :
    ThetaLowerSegment 32841984 32858368 (3283565358259 / 100000) (3285197427219 / 100000) := by
  exact
    packedTile8192 32841984 32858368 11 943 5730 25 _ _ (10817 / 625) (1730723 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32858368 :
    ThetaLowerSegment 32858368 32874752 (3285197427219 / 100000) (3286800120239 / 100000) := by
  exact
    packedTile8192 32858368 32874752 11 926 5732 25 _ _ (173077 / 10000) (1730773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32874752 :
    ThetaLowerSegment 32874752 32891136 (3286800120239 / 100000) (3288480746459 / 100000) := by
  exact
    packedTile8192 32874752 32891136 11 971 5733 25 _ _ (86541 / 5000) (1730823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32891136 :
    ThetaLowerSegment 32891136 32907520 (3288480746459 / 100000) (3290118149479 / 100000) := by
  exact
    packedTile8192 32891136 32907520 11 946 5735 25 _ _ (173087 / 10000) (1730873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32907520 :
    ThetaLowerSegment 32907520 32923904 (3290118149479 / 100000) (3291743483359 / 100000) := by
  exact
    packedTile8192 32907520 32923904 11 939 5736 25 _ _ (43273 / 2500) (1730923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32923904 :
    ThetaLowerSegment 32923904 32940288 (3291743483359 / 100000) (3293425985227 / 100000) := by
  exact
    packedTile8192 32923904 32940288 11 972 5737 25 _ _ (1730969 / 100000) (432743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32940288 :
    ThetaLowerSegment 32940288 32956672 (3293425985227 / 100000) (1647544747243 / 50000) := by
  exact
    packedTile8192 32940288 32956672 11 961 5739 25 _ _ (1731019 / 100000) (865511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32956672 :
    ThetaLowerSegment 32956672 32973056 (1647544747243 / 50000) (412092616789 / 12500) := by
  exact
    packedTile8192 32956672 32973056 11 954 5740 25 _ _ (1731069 / 100000) (54096 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32973056 :
    ThetaLowerSegment 32973056 32989440 (412092616789 / 12500) (824598971019 / 25000) := by
  exact
    packedTile8192 32973056 32989440 11 956 5742 25 _ _ (1731119 / 100000) (865561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell32989440 :
    ThetaLowerSegment 32989440 33005824 (824598971019 / 25000) (825006228291 / 25000) := by
  exact
    packedTile8192 32989440 33005824 11 941 5743 25 _ _ (54099 / 3125) (1731171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33005824 :
    ThetaLowerSegment 33005824 33022208 (825006228291 / 25000) (412705233847 / 12500) := by
  exact
    packedTile8192 33005824 33022208 11 934 5745 25 _ _ (865609 / 50000) (1731221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33022208 :
    ThetaLowerSegment 33022208 33038592 (412705233847 / 12500) (825810823419 / 25000) := by
  exact
    packedTile8192 33022208 33038592 11 925 5746 25 _ _ (432817 / 25000) (1731271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33038592 :
    ThetaLowerSegment 33038592 33054976 (825810823419 / 25000) (1652426709243 / 50000) := by
  exact
    packedTile8192 33038592 33054976 11 930 5747 25 _ _ (1731317 / 100000) (43283 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33054976 :
    ThetaLowerSegment 33054976 33071360 (1652426709243 / 50000) (330646705253 / 10000) := by
  exact
    packedTile8192 33054976 33071360 11 932 5749 25 _ _ (1731367 / 100000) (173137 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33071360 :
    ThetaLowerSegment 33071360 33087744 (330646705253 / 10000) (1654062008821 / 50000) := by
  exact
    packedTile8192 33071360 33087744 11 957 5750 25 _ _ (216427 / 12500) (1731419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33087744 :
    ThetaLowerSegment 33087744 33104128 (1654062008821 / 50000) (827440063253 / 25000) := by
  exact
    packedTile8192 33087744 33104128 11 945 5752 25 _ _ (865733 / 50000) (1731469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33104128 :
    ThetaLowerSegment 33104128 33120512 (827440063253 / 25000) (1655699133101 / 50000) := by
  exact
    packedTile8192 33104128 33120512 11 946 5753 25 _ _ (346303 / 20000) (865759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33120512 :
    ThetaLowerSegment 33120512 33136896 (1655699133101 / 50000) (828262544803 / 25000) := by
  exact
    packedTile8192 33120512 33136896 11 954 5755 25 _ _ (346313 / 20000) (108223 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33136896 :
    ThetaLowerSegment 33136896 33153280 (828262544803 / 25000) (207169316589 / 6250) := by
  exact
    packedTile8192 33136896 33153280 11 958 5756 25 _ _ (865807 / 50000) (1731617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33153280 :
    ThetaLowerSegment 33153280 33169664 (207169316589 / 6250) (103636770558 / 3125) := by
  exact
    packedTile8192 33153280 33169664 11 963 5757 25 _ _ (108229 / 6250) (1731667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33169664 :
    ThetaLowerSegment 33169664 33186048 (103636770558 / 3125) (3317999272937 / 100000) := by
  exact
    packedTile8192 33169664 33186048 11 937 5759 25 _ _ (1731713 / 100000) (432929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33186048 :
    ThetaLowerSegment 33186048 33202432 (3317999272937 / 100000) (1659809235671 / 50000) := by
  exact
    packedTile8192 33186048 33202432 11 935 5760 25 _ _ (1731763 / 100000) (865883 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33202432 :
    ThetaLowerSegment 33202432 33218816 (1659809235671 / 50000) (1660623187311 / 50000) := by
  exact
    packedTile8192 33202432 33218816 11 940 5762 25 _ _ (432953 / 25000) (346363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33218816 :
    ThetaLowerSegment 33218816 33235200 (1660623187311 / 50000) (3322889910711 / 100000) := by
  exact
    packedTile8192 33218816 33235200 11 949 5763 25 _ _ (1731861 / 100000) (216483 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33235200 :
    ThetaLowerSegment 33235200 33251584 (3322889910711 / 100000) (3324556009093 / 100000) := by
  exact
    packedTile8192 33235200 33251584 11 962 5764 25 _ _ (1731911 / 100000) (865957 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33251584 :
    ThetaLowerSegment 33251584 33267968 (3324556009093 / 100000) (3326229082453 / 100000) := by
  exact
    packedTile8192 33251584 33267968 11 966 5766 25 _ _ (43299 / 2500) (1731963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33267968 :
    ThetaLowerSegment 33267968 33284352 (3326229082453 / 100000) (3327839850823 / 100000) := by
  exact
    packedTile8192 33267968 33284352 11 930 5767 25 _ _ (1732009 / 100000) (433003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33284352 :
    ThetaLowerSegment 33284352 33300736 (3327839850823 / 100000) (3329507822677 / 100000) := by
  exact
    packedTile8192 33284352 33300736 11 963 5769 25 _ _ (866029 / 50000) (1732061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33300736 :
    ThetaLowerSegment 33300736 33317120 (3329507822677 / 100000) (3331144664737 / 100000) := by
  exact
    packedTile8192 33300736 33317120 11 945 5770 25 _ _ (433027 / 25000) (1732111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33317120 :
    ThetaLowerSegment 33317120 33333504 (3331144664737 / 100000) (3332824857027 / 100000) := by
  exact
    packedTile8192 33317120 33333504 11 970 5772 25 _ _ (1732157 / 100000) (10826 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33333504 :
    ThetaLowerSegment 33333504 33349888 (3332824857027 / 100000) (3334439273019 / 100000) := by
  exact
    packedTile8192 33333504 33349888 11 932 5773 25 _ _ (866103 / 50000) (1732209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33349888 :
    ThetaLowerSegment 33349888 33366272 (3334439273019 / 100000) (3336109166839 / 100000) := by
  exact
    packedTile8192 33349888 33366272 11 964 5774 25 _ _ (346451 / 20000) (866129 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33366272 :
    ThetaLowerSegment 33366272 33382656 (3336109166839 / 100000) (667550624667 / 20000) := by
  exact
    packedTile8192 33366272 33382656 11 949 5776 25 _ _ (108269 / 6250) (1732307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33382656 :
    ThetaLowerSegment 33382656 33399040 (667550624667 / 20000) (104356376742 / 3125) := by
  exact
    packedTile8192 33382656 33399040 11 953 5777 25 _ _ (1732353 / 100000) (433089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33399040 :
    ThetaLowerSegment 33399040 33415424 (104356376742 / 3125) (334107235887 / 10000) := by
  exact
    packedTile8192 33399040 33415424 11 963 5779 25 _ _ (866201 / 50000) (346481 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33415424 :
    ThetaLowerSegment 33415424 33431808 (334107235887 / 10000) (3342699130359 / 100000) := by
  exact
    packedTile8192 33415424 33431808 11 939 5780 25 _ _ (1732451 / 100000) (866227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33431808 :
    ThetaLowerSegment 33431808 33448192 (3342699130359 / 100000) (3344324215359 / 100000) := by
  exact
    packedTile8192 33431808 33448192 11 938 5782 25 _ _ (693 / 40) (1732503 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33448192 :
    ThetaLowerSegment 33448192 33464576 (3344324215359 / 100000) (669191948323 / 20000) := by
  exact
    packedTile8192 33448192 33464576 11 944 5783 25 _ _ (1732549 / 100000) (216569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33464576 :
    ThetaLowerSegment 33464576 33480960 (669191948323 / 20000) (3347600511921 / 100000) := by
  exact
    packedTile8192 33464576 33480960 11 947 5784 25 _ _ (866299 / 50000) (1732601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33480960 :
    ThetaLowerSegment 33480960 33497344 (3347600511921 / 100000) (3349253457159 / 100000) := by
  exact
    packedTile8192 33480960 33497344 11 954 5786 25 _ _ (1732647 / 100000) (34653 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33497344 :
    ThetaLowerSegment 33497344 33513728 (3349253457159 / 100000) (3350861399047 / 100000) := by
  exact
    packedTile8192 33497344 33513728 11 928 5787 25 _ _ (216587 / 12500) (1732699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33513728 :
    ThetaLowerSegment 33513728 33530112 (3350861399047 / 100000) (3352452058957 / 100000) := by
  exact
    packedTile8192 33513728 33530112 11 918 5789 25 _ _ (346549 / 20000) (433187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33530112 :
    ThetaLowerSegment 33530112 33546496 (3352452058957 / 100000) (3354098213257 / 100000) := by
  exact
    packedTile8192 33530112 33546496 11 950 5790 25 _ _ (866397 / 50000) (1732797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33546496 :
    ThetaLowerSegment 33546496 33562880 (3354098213257 / 100000) (41947476653 / 1250) := by
  exact
    packedTile8192 33546496 33562880 11 981 5791 25 _ _ (1732843 / 100000) (866423 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33562880 :
    ThetaLowerSegment 33562880 33579264 (41947476653 / 1250) (419677081671 / 12500) := by
  exact
    packedTile8192 33562880 33579264 11 934 5793 25 _ _ (433223 / 25000) (346579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33579264 :
    ThetaLowerSegment 33579264 33595648 (419677081671 / 12500) (209939267973 / 6250) := by
  exact
    packedTile8192 33579264 33595648 11 930 5794 25 _ _ (86647 / 5000) (1732943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33595648 :
    ThetaLowerSegment 33595648 33612032 (209939267973 / 6250) (3360634768371 / 100000) := by
  exact
    packedTile8192 33595648 33612032 11 927 5796 25 _ _ (1732989 / 100000) (54156 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33612032 :
    ThetaLowerSegment 33612032 33628416 (3360634768371 / 100000) (3362270756243 / 100000) := by
  exact
    packedTile8192 33612032 33628416 11 944 5797 25 _ _ (866519 / 50000) (1733041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33628416 :
    ThetaLowerSegment 33628416 33644800 (3362270756243 / 100000) (134555717027 / 4000) := by
  exact
    packedTile8192 33628416 33644800 11 936 5799 25 _ _ (1733087 / 100000) (173309 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33644800 :
    ThetaLowerSegment 33644800 33661184 (134555717027 / 4000) (336555153587 / 10000) := by
  exact
    packedTile8192 33644800 33661184 11 957 5800 25 _ _ (346627 / 20000) (866569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33661184 :
    ThetaLowerSegment 33661184 33677568 (336555153587 / 10000) (13468757579 / 400) := by
  exact
    packedTile8192 33661184 33677568 11 945 5801 25 _ _ (54162 / 3125) (1733187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33677568 :
    ThetaLowerSegment 33677568 33693952 (13468757579 / 400) (1684419716283 / 50000) := by
  exact
    packedTile8192 33677568 33693952 11 952 5803 25 _ _ (1733233 / 100000) (433309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33693952 :
    ThetaLowerSegment 33693952 33710336 (1684419716283 / 50000) (421309889549 / 12500) := by
  exact
    packedTile8192 33693952 33710336 11 946 5804 25 _ _ (1733281 / 100000) (433321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33710336 :
    ThetaLowerSegment 33710336 33726720 (421309889549 / 12500) (843026244983 / 25000) := by
  exact
    packedTile8192 33710336 33726720 11 938 5806 25 _ _ (173333 / 10000) (1733333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33726720 :
    ThetaLowerSegment 33726720 33743104 (843026244983 / 25000) (3373708355507 / 100000) := by
  exact
    packedTile8192 33726720 33743104 11 925 5807 25 _ _ (1733379 / 100000) (866691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33743104 :
    ThetaLowerSegment 33743104 33759488 (3373708355507 / 100000) (421926539281 / 12500) := by
  exact
    packedTile8192 33743104 33759488 11 983 5808 25 _ _ (1733427 / 100000) (173343 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33759488 :
    ThetaLowerSegment 33759488 33775872 (421926539281 / 12500) (844266945957 / 25000) := by
  exact
    packedTile8192 33759488 33775872 11 955 5810 25 _ _ (433369 / 25000) (1733479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33775872 :
    ThetaLowerSegment 33775872 33792256 (844266945957 / 25000) (844679524669 / 25000) := by
  exact
    packedTile8192 33775872 33792256 11 952 5811 25 _ _ (433381 / 25000) (1733527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33792256 :
    ThetaLowerSegment 33792256 33808640 (844679524669 / 25000) (338030951869 / 10000) := by
  exact
    packedTile8192 33792256 33808640 11 918 5813 25 _ _ (1733573 / 100000) (216697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33808640 :
    ThetaLowerSegment 33808640 33825024 (338030951869 / 10000) (3382048340553 / 100000) := by
  exact
    packedTile8192 33808640 33825024 11 1003 5814 25 _ _ (1733621 / 100000) (216703 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33825024 :
    ThetaLowerSegment 33825024 33841408 (3382048340553 / 100000) (3383674523013 / 100000) := by
  exact
    packedTile8192 33825024 33841408 11 938 5815 25 _ _ (173367 / 10000) (1733673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33841408 :
    ThetaLowerSegment 33841408 33857792 (3383674523013 / 100000) (3385290348189 / 100000) := by
  exact
    packedTile8192 33841408 33857792 11 932 5817 25 _ _ (866859 / 50000) (1733721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33857792 :
    ThetaLowerSegment 33857792 33874176 (3385290348189 / 100000) (3386928757059 / 100000) := by
  exact
    packedTile8192 33857792 33874176 11 945 5818 25 _ _ (866883 / 50000) (1733769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33874176 :
    ThetaLowerSegment 33874176 33890560 (3386928757059 / 100000) (3388603622349 / 100000) := by
  exact
    packedTile8192 33874176 33890560 11 966 5820 25 _ _ (346763 / 20000) (866909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33890560 :
    ThetaLowerSegment 33890560 33906944 (3388603622349 / 100000) (847550127543 / 25000) := by
  exact
    packedTile8192 33890560 33906944 11 921 5821 25 _ _ (1733863 / 100000) (866933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33906944 :
    ThetaLowerSegment 33906944 33923328 (847550127543 / 25000) (847962798599 / 25000) := by
  exact
    packedTile8192 33906944 33923328 11 952 5822 25 _ _ (216739 / 12500) (346783 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33923328 :
    ThetaLowerSegment 33923328 33939712 (847962798599 / 25000) (848365510809 / 25000) := by
  exact
    packedTile8192 33923328 33939712 11 929 5824 25 _ _ (43349 / 2500) (1733963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33939712 :
    ThetaLowerSegment 33939712 33956096 (848365510809 / 25000) (848760431131 / 25000) := by
  exact
    packedTile8192 33939712 33956096 11 911 5825 25 _ _ (216751 / 12500) (1734011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33956096 :
    ThetaLowerSegment 33956096 33972480 (848760431131 / 25000) (169833673561 / 5000) := by
  exact
    packedTile8192 33956096 33972480 11 941 5827 25 _ _ (216757 / 12500) (1734059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33972480 :
    ThetaLowerSegment 33972480 33988864 (169833673561 / 5000) (679662440089 / 20000) := by
  exact
    packedTile8192 33972480 33988864 11 945 5828 25 _ _ (346821 / 20000) (433527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell33988864 :
    ThetaLowerSegment 33988864 34005248 (679662440089 / 20000) (424994305417 / 12500) := by
  exact
    packedTile8192 33988864 34005248 11 947 5829 25 _ _ (1734153 / 100000) (433539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34005248 :
    ThetaLowerSegment 34005248 34021632 (424994305417 / 12500) (850392679667 / 25000) := by
  exact
    packedTile8192 34005248 34021632 11 932 5831 25 _ _ (1734201 / 100000) (433551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34021632 :
    ThetaLowerSegment 34021632 34038016 (850392679667 / 25000) (3403185304487 / 100000) := by
  exact
    packedTile8192 34021632 34038016 11 931 5832 25 _ _ (1734249 / 100000) (433563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34038016 :
    ThetaLowerSegment 34038016 34054400 (3403185304487 / 100000) (680964496171 / 20000) := by
  exact
    packedTile8192 34038016 34054400 11 944 5834 25 _ _ (1734297 / 100000) (17343 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34054400 :
    ThetaLowerSegment 34054400 34070784 (680964496171 / 20000) (340642328129 / 10000) := by
  exact
    packedTile8192 34054400 34070784 11 923 5835 25 _ _ (346869 / 20000) (433587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34070784 :
    ThetaLowerSegment 34070784 34087168 (340642328129 / 10000) (1704037212189 / 50000) := by
  exact
    packedTile8192 34070784 34087168 11 952 5837 25 _ _ (867197 / 50000) (1734397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34087168 :
    ThetaLowerSegment 34087168 34103552 (1704037212189 / 50000) (340969786209 / 10000) := by
  exact
    packedTile8192 34087168 34103552 11 936 5838 25 _ _ (867221 / 50000) (346889 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34103552 :
    ThetaLowerSegment 34103552 34119936 (340969786209 / 10000) (170567541553 / 5000) := by
  exact
    packedTile8192 34103552 34119936 11 953 5839 25 _ _ (173449 / 10000) (1734493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34119936 :
    ThetaLowerSegment 34119936 34136320 (170567541553 / 5000) (853233182429 / 25000) := by
  exact
    packedTile8192 34119936 34136320 11 912 5841 25 _ _ (867269 / 50000) (1734541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34136320 :
    ThetaLowerSegment 34136320 34152704 (853233182429 / 25000) (853646013897 / 25000) := by
  exact
    packedTile8192 34136320 34152704 11 952 5842 25 _ _ (867293 / 50000) (1734589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34152704 :
    ThetaLowerSegment 34152704 34169088 (853646013897 / 25000) (427022923517 / 12500) := by
  exact
    packedTile8192 34152704 34169088 11 922 5844 25 _ _ (867317 / 50000) (1734637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34169088 :
    ThetaLowerSegment 34169088 34185472 (427022923517 / 12500) (42722501397 / 1250) := by
  exact
    packedTile8192 34169088 34185472 11 932 5845 25 _ _ (867341 / 50000) (346937 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34185472 :
    ThetaLowerSegment 34185472 34201856 (42722501397 / 1250) (21371225396 / 625) := by
  exact
    packedTile8192 34185472 34201856 11 920 5846 25 _ _ (173473 / 10000) (1734733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34201856 :
    ThetaLowerSegment 34201856 34218240 (21371225396 / 625) (68421055527 / 2000) := by
  exact
    packedTile8192 34201856 34218240 11 955 5848 25 _ _ (867389 / 50000) (1734781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34218240 :
    ThetaLowerSegment 34218240 34234624 (68421055527 / 2000) (136906715937 / 4000) := by
  exact
    packedTile8192 34218240 34234624 11 931 5849 25 _ _ (69393 / 4000) (433707 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34234624 :
    ThetaLowerSegment 34234624 34251008 (136906715937 / 4000) (3424267451331 / 100000) := by
  exact
    packedTile8192 34234624 34251008 11 922 5851 25 _ _ (1734873 / 100000) (433719 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34251008 :
    ThetaLowerSegment 34251008 34267392 (3424267451331 / 100000) (856483677603 / 25000) := by
  exact
    packedTile8192 34251008 34267392 11 961 5852 25 _ _ (1734921 / 100000) (433731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34267392 :
    ThetaLowerSegment 34267392 34283776 (856483677603 / 25000) (3427570786179 / 100000) := by
  exact
    packedTile8192 34267392 34283776 11 943 5853 25 _ _ (1734969 / 100000) (433743 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34283776 :
    ThetaLowerSegment 34283776 34300160 (3427570786179 / 100000) (107163041166 / 3125) := by
  exact
    packedTile8192 34283776 34300160 11 949 5855 25 _ _ (1735017 / 100000) (86751 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34300160 :
    ThetaLowerSegment 34300160 34316544 (107163041166 / 3125) (3430818782307 / 100000) := by
  exact
    packedTile8192 34300160 34316544 11 923 5856 25 _ _ (347013 / 20000) (433767 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34316544 :
    ThetaLowerSegment 34316544 34332928 (3430818782307 / 100000) (3432428966243 / 100000) := by
  exact
    packedTile8192 34316544 34332928 11 928 5858 25 _ _ (216889 / 12500) (347023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34332928 :
    ThetaLowerSegment 34332928 34349312 (3432428966243 / 100000) (3434021843123 / 100000) := by
  exact
    packedTile8192 34332928 34349312 11 918 5859 25 _ _ (43379 / 2500) (1735163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34349312 :
    ThetaLowerSegment 34349312 34365696 (3434021843123 / 100000) (3435626910523 / 100000) := by
  exact
    packedTile8192 34349312 34365696 11 925 5860 25 _ _ (216901 / 12500) (1735211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34365696 :
    ThetaLowerSegment 34365696 34382080 (3435626910523 / 100000) (3437258050223 / 100000) := by
  exact
    packedTile8192 34365696 34382080 11 940 5862 25 _ _ (347051 / 20000) (867629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34382080 :
    ThetaLowerSegment 34382080 34398464 (3437258050223 / 100000) (687779235251 / 20000) := by
  exact
    packedTile8192 34382080 34398464 11 944 5863 25 _ _ (1735303 / 100000) (867653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34398464 :
    ThetaLowerSegment 34398464 34414848 (687779235251 / 20000) (3440575996023 / 100000) := by
  exact
    packedTile8192 34398464 34414848 11 968 5865 25 _ _ (1735351 / 100000) (867677 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34414848 :
    ThetaLowerSegment 34414848 34431232 (3440575996023 / 100000) (3442210740939 / 100000) := by
  exact
    packedTile8192 34414848 34431232 11 942 5866 25 _ _ (867699 / 50000) (1735401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34431232 :
    ThetaLowerSegment 34431232 34447616 (3442210740939 / 100000) (3443777848677 / 100000) := by
  exact
    packedTile8192 34431232 34447616 11 903 5867 25 _ _ (867723 / 50000) (1735449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34447616 :
    ThetaLowerSegment 34447616 34464000 (3443777848677 / 100000) (3445449129399 / 100000) := by
  exact
    packedTile8192 34447616 34464000 11 963 5869 25 _ _ (867747 / 50000) (1735497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34464000 :
    ThetaLowerSegment 34464000 34480384 (3445449129399 / 100000) (1723560227691 / 50000) := by
  exact
    packedTile8192 34464000 34480384 11 963 5870 25 _ _ (1735541 / 100000) (216943 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34480384 :
    ThetaLowerSegment 34480384 34496768 (1723560227691 / 50000) (3448774471699 / 100000) := by
  exact
    packedTile8192 34480384 34496768 11 953 5872 25 _ _ (1735589 / 100000) (216949 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34496768 :
    ThetaLowerSegment 34496768 34513152 (3448774471699 / 100000) (3450419854627 / 100000) := by
  exact
    packedTile8192 34496768 34513152 11 948 5873 25 _ _ (433909 / 25000) (1735639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34513152 :
    ThetaLowerSegment 34513152 34529536 (3450419854627 / 100000) (3452101732423 / 100000) := by
  exact
    packedTile8192 34513152 34529536 11 969 5874 25 _ _ (433921 / 25000) (1735687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34529536 :
    ThetaLowerSegment 34529536 34545920 (3452101732423 / 100000) (1726867527647 / 50000) := by
  exact
    packedTile8192 34529536 34545920 11 941 5876 25 _ _ (1735731 / 100000) (867867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34545920 :
    ThetaLowerSegment 34545920 34562304 (1726867527647 / 50000) (3455358008659 / 100000) := by
  exact
    packedTile8192 34545920 34562304 11 935 5877 25 _ _ (1735779 / 100000) (867891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34562304 :
    ThetaLowerSegment 34562304 34578688 (3455358008659 / 100000) (138279656837 / 4000) := by
  exact
    packedTile8192 34562304 34578688 11 941 5878 25 _ _ (867913 / 50000) (1735829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34578688 :
    ThetaLowerSegment 34578688 34595072 (138279656837 / 4000) (1729326325693 / 50000) := by
  exact
    packedTile8192 34578688 34595072 11 957 5880 25 _ _ (1735873 / 100000) (433969 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34595072 :
    ThetaLowerSegment 34595072 34611456 (1729326325693 / 50000) (865066764479 / 25000) := by
  exact
    packedTile8192 34595072 34611456 11 930 5881 25 _ _ (1735921 / 100000) (433981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34611456 :
    ThetaLowerSegment 34611456 34627840 (865066764479 / 25000) (865468641071 / 25000) := by
  exact
    packedTile8192 34611456 34627840 11 926 5883 25 _ _ (54249 / 3125) (1735971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34627840 :
    ThetaLowerSegment 34627840 34644224 (865468641071 / 25000) (432943510343 / 12500) := by
  exact
    packedTile8192 34627840 34644224 11 964 5884 25 _ _ (347203 / 20000) (868009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34644224 :
    ThetaLowerSegment 34644224 34660608 (432943510343 / 12500) (1732543117281 / 50000) := by
  exact
    packedTile8192 34644224 34660608 11 886 5885 25 _ _ (1736063 / 100000) (868033 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34660608 :
    ThetaLowerSegment 34660608 34676992 (1732543117281 / 50000) (433334780929 / 12500) := by
  exact
    packedTile8192 34660608 34676992 11 917 5887 25 _ _ (173611 / 10000) (1736113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34676992 :
    ThetaLowerSegment 34676992 34693376 (433334780929 / 12500) (867084503381 / 25000) := by
  exact
    packedTile8192 34676992 34693376 11 956 5888 25 _ _ (1736157 / 100000) (10851 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34693376 :
    ThetaLowerSegment 34693376 34709760 (867084503381 / 25000) (433745170533 / 12500) := by
  exact
    packedTile8192 34693376 34709760 11 935 5890 25 _ _ (434051 / 25000) (1736207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34709760 :
    ThetaLowerSegment 34709760 34726144 (433745170533 / 12500) (173582536873 / 5000) := by
  exact
    packedTile8192 34709760 34726144 11 973 5891 25 _ _ (434063 / 25000) (347251 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34726144 :
    ThetaLowerSegment 34726144 34742528 (173582536873 / 5000) (3473229033251 / 100000) := by
  exact
    packedTile8192 34726144 34742528 11 909 5892 25 _ _ (1736299 / 100000) (868151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34742528 :
    ThetaLowerSegment 34742528 34758912 (3473229033251 / 100000) (3474812580803 / 100000) := by
  exact
    packedTile8192 34742528 34758912 11 912 5894 25 _ _ (868173 / 50000) (1736349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34758912 :
    ThetaLowerSegment 34758912 34775296 (3474812580803 / 100000) (695297292731 / 20000) := by
  exact
    packedTile8192 34758912 34775296 11 964 5895 25 _ _ (1736393 / 100000) (434099 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34775296 :
    ThetaLowerSegment 34775296 34791680 (695297292731 / 20000) (695629300059 / 20000) := by
  exact
    packedTile8192 34775296 34791680 11 956 5897 25 _ _ (43411 / 2500) (1736443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34791680 :
    ThetaLowerSegment 34791680 34808064 (695629300059 / 20000) (3479817000789 / 100000) := by
  exact
    packedTile8192 34791680 34808064 11 962 5898 25 _ _ (1736487 / 100000) (173649 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34808064 :
    ThetaLowerSegment 34808064 34824448 (3479817000789 / 100000) (696284311641 / 20000) := by
  exact
    packedTile8192 34808064 34824448 11 924 5899 25 _ _ (868267 / 50000) (1736537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34824448 :
    ThetaLowerSegment 34824448 34840832 (696284311641 / 20000) (696603842729 / 20000) := by
  exact
    packedTile8192 34824448 34840832 11 920 5901 25 _ _ (868291 / 50000) (347317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34840832 :
    ThetaLowerSegment 34840832 34857216 (696603842729 / 20000) (174233884717 / 5000) := by
  exact
    packedTile8192 34840832 34857216 11 955 5902 25 _ _ (1736629 / 100000) (217079 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34857216 :
    ThetaLowerSegment 34857216 34873600 (174233884717 / 5000) (871591435853 / 25000) := by
  exact
    packedTile8192 34857216 34873600 11 972 5904 25 _ _ (434169 / 25000) (1736679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34873600 :
    ThetaLowerSegment 34873600 34889984 (871591435853 / 25000) (1744014762023 / 50000) := by
  exact
    packedTile8192 34873600 34889984 11 958 5905 25 _ _ (1736723 / 100000) (868363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34889984 :
    ThetaLowerSegment 34889984 34906368 (1744014762023 / 50000) (1744824096843 / 50000) := by
  exact
    packedTile8192 34889984 34906368 11 932 5906 25 _ _ (173677 / 10000) (1736773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34906368 :
    ThetaLowerSegment 34906368 34922752 (1744824096843 / 50000) (1745664715787 / 50000) := by
  exact
    packedTile8192 34906368 34922752 11 968 5908 25 _ _ (108551 / 6250) (1736819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34922752 :
    ThetaLowerSegment 34922752 34939136 (1745664715787 / 50000) (3492970767109 / 100000) := by
  exact
    packedTile8192 34922752 34939136 11 945 5909 25 _ _ (1736863 / 100000) (868433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34939136 :
    ThetaLowerSegment 34939136 34955520 (3492970767109 / 100000) (3494612147059 / 100000) := by
  exact
    packedTile8192 34939136 34955520 11 945 5910 25 _ _ (173691 / 10000) (1736913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34955520 :
    ThetaLowerSegment 34955520 34971904 (3494612147059 / 100000) (699255230373 / 20000) := by
  exact
    packedTile8192 34955520 34971904 11 958 5912 25 _ _ (1736957 / 100000) (10856 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34971904 :
    ThetaLowerSegment 34971904 34988288 (699255230373 / 20000) (3497867247529 / 100000) := by
  exact
    packedTile8192 34971904 34988288 11 916 5913 25 _ _ (434251 / 25000) (1737007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell34988288 :
    ThetaLowerSegment 34988288 35004672 (3497867247529 / 100000) (3499496601367 / 100000) := by
  exact
    packedTile8192 34988288 35004672 11 938 5915 25 _ _ (1737051 / 100000) (868527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35004672 :
    ThetaLowerSegment 35004672 35021056 (3499496601367 / 100000) (3501124262193 / 100000) := by
  exact
    packedTile8192 35004672 35021056 11 937 5916 25 _ _ (868549 / 50000) (1737101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35021056 :
    ThetaLowerSegment 35021056 35037440 (3501124262193 / 100000) (1751382932109 / 50000) := by
  exact
    packedTile8192 35021056 35037440 11 945 5917 25 _ _ (347429 / 20000) (434287 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35037440 :
    ThetaLowerSegment 35037440 35053824 (1751382932109 / 50000) (876093625771 / 25000) := by
  exact
    packedTile8192 35037440 35053824 11 926 5919 25 _ _ (1737191 / 100000) (868597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35053824 :
    ThetaLowerSegment 35053824 35070208 (876093625771 / 25000) (35059936089 / 1000) := by
  exact
    packedTile8192 35053824 35070208 11 932 5920 25 _ _ (868619 / 50000) (1737241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35070208 :
    ThetaLowerSegment 35070208 35086592 (35059936089 / 1000) (70152185679 / 2000) := by
  exact
    packedTile8192 35070208 35086592 11 930 5922 25 _ _ (347457 / 20000) (217161 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35086592 :
    ThetaLowerSegment 35086592 35102976 (70152185679 / 2000) (3509254536407 / 100000) := by
  exact
    packedTile8192 35086592 35102976 11 947 5923 25 _ _ (1737331 / 100000) (868667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35102976 :
    ThetaLowerSegment 35102976 35119360 (3509254536407 / 100000) (3510887671727 / 100000) := by
  exact
    packedTile8192 35102976 35119360 11 940 5924 25 _ _ (868689 / 50000) (1737381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35119360 :
    ThetaLowerSegment 35119360 35135744 (3510887671727 / 100000) (878127172313 / 25000) := by
  exact
    packedTile8192 35119360 35135744 11 933 5926 25 _ _ (69497 / 4000) (434357 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35135744 :
    ThetaLowerSegment 35135744 35152128 (878127172313 / 25000) (3514185348767 / 100000) := by
  exact
    packedTile8192 35135744 35152128 11 965 5927 25 _ _ (1737471 / 100000) (868737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35152128 :
    ThetaLowerSegment 35152128 35168512 (3514185348767 / 100000) (3515856841083 / 100000) := by
  exact
    packedTile8192 35152128 35168512 11 962 5928 25 _ _ (868759 / 50000) (1737521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35168512 :
    ThetaLowerSegment 35168512 35184896 (3515856841083 / 100000) (439683879871 / 12500) := by
  exact
    packedTile8192 35168512 35184896 11 929 5930 25 _ _ (347513 / 20000) (54299 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35184896 :
    ThetaLowerSegment 35184896 35201280 (439683879871 / 12500) (3519074853921 / 100000) := by
  exact
    packedTile8192 35184896 35201280 11 923 5931 25 _ _ (1737611 / 100000) (868807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35201280 :
    ThetaLowerSegment 35201280 35217664 (3519074853921 / 100000) (3520732579653 / 100000) := by
  exact
    packedTile8192 35201280 35217664 11 954 5933 25 _ _ (868829 / 50000) (1737661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35217664 :
    ThetaLowerSegment 35217664 35234048 (3520732579653 / 100000) (3522402513197 / 100000) := by
  exact
    packedTile8192 35217664 35234048 11 961 5934 25 _ _ (217213 / 12500) (1737707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35234048 :
    ThetaLowerSegment 35234048 35250432 (3522402513197 / 100000) (3524063803153 / 100000) := by
  exact
    packedTile8192 35234048 35250432 11 956 5935 25 _ _ (1737751 / 100000) (868877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35250432 :
    ThetaLowerSegment 35250432 35266816 (3524063803153 / 100000) (1762856486253 / 50000) := by
  exact
    packedTile8192 35250432 35266816 11 949 5937 25 _ _ (1737797 / 100000) (8689 / 500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35266816 :
    ThetaLowerSegment 35266816 35283200 (1762856486253 / 50000) (1763651549883 / 50000) := by
  exact
    packedTile8192 35266816 35283200 11 915 5938 25 _ _ (434461 / 25000) (1737847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35283200 :
    ThetaLowerSegment 35283200 35299584 (1763651549883 / 50000) (441114699947 / 12500) := by
  exact
    packedTile8192 35283200 35299584 11 929 5939 25 _ _ (173789 / 10000) (1737893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35299584 :
    ThetaLowerSegment 35299584 35315968 (441114699947 / 12500) (441326728261 / 12500) := by
  exact
    packedTile8192 35299584 35315968 11 976 5941 25 _ _ (1737937 / 100000) (86897 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35315968 :
    ThetaLowerSegment 35315968 35332352 (441326728261 / 12500) (3532256220023 / 100000) := by
  exact
    packedTile8192 35315968 35332352 11 945 5942 25 _ _ (1737983 / 100000) (868993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35332352 :
    ThetaLowerSegment 35332352 35348736 (3532256220023 / 100000) (353389518137 / 10000) := by
  exact
    packedTile8192 35332352 35348736 11 943 5944 25 _ _ (1738029 / 100000) (108627 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35348736 :
    ThetaLowerSegment 35348736 35365120 (353389518137 / 10000) (353549421129 / 10000) := by
  exact
    packedTile8192 35348736 35365120 11 920 5945 25 _ _ (434519 / 25000) (1738079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35365120 :
    ThetaLowerSegment 35365120 35381504 (353549421129 / 10000) (884280707901 / 25000) := by
  exact
    packedTile8192 35365120 35381504 11 937 5946 25 _ _ (869061 / 50000) (2781 / 160) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35381504 :
    ThetaLowerSegment 35381504 35397888 (884280707901 / 25000) (884701344557 / 25000) := by
  exact
    packedTile8192 35381504 35397888 11 968 5948 25 _ _ (217271 / 12500) (1738171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35397888 :
    ThetaLowerSegment 35397888 35414272 (884701344557 / 25000) (3540486232133 / 100000) := by
  exact
    packedTile8192 35397888 35414272 11 967 5949 25 _ _ (347643 / 20000) (869109 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35414272 :
    ThetaLowerSegment 35414272 35430656 (3540486232133 / 100000) (3542116720951 / 100000) := by
  exact
    packedTile8192 35414272 35430656 11 938 5950 25 _ _ (1738261 / 100000) (217283 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35430656 :
    ThetaLowerSegment 35430656 35447040 (3542116720951 / 100000) (3543740299689 / 100000) := by
  exact
    packedTile8192 35430656 35447040 11 934 5952 25 _ _ (1738307 / 100000) (173831 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35447040 :
    ThetaLowerSegment 35447040 35463424 (3543740299689 / 100000) (3545367399033 / 100000) := by
  exact
    packedTile8192 35447040 35463424 11 936 5953 25 _ _ (869177 / 50000) (1738357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35463424 :
    ThetaLowerSegment 35463424 35479808 (3545367399033 / 100000) (3546971942233 / 100000) := by
  exact
    packedTile8192 35463424 35479808 11 923 5955 25 _ _ (2173 / 125) (1738403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35479808 :
    ThetaLowerSegment 35479808 35496192 (3546971942233 / 100000) (3548628681271 / 100000) := by
  exact
    packedTile8192 35479808 35496192 11 953 5956 25 _ _ (869223 / 50000) (1738449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35496192 :
    ThetaLowerSegment 35496192 35512576 (3548628681271 / 100000) (3550245478831 / 100000) := by
  exact
    packedTile8192 35496192 35512576 11 930 5957 25 _ _ (434623 / 25000) (347699 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35512576 :
    ThetaLowerSegment 35512576 35528960 (3550245478831 / 100000) (3551888397241 / 100000) := by
  exact
    packedTile8192 35512576 35528960 11 945 5959 25 _ _ (869269 / 50000) (1738541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35528960 :
    ThetaLowerSegment 35528960 35545344 (3551888397241 / 100000) (3553573085137 / 100000) := by
  exact
    packedTile8192 35528960 35545344 11 969 5960 25 _ _ (217323 / 12500) (1738587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35545344 :
    ThetaLowerSegment 35545344 35561728 (3553573085137 / 100000) (3555214351857 / 100000) := by
  exact
    packedTile8192 35545344 35561728 11 944 5961 25 _ _ (173863 / 10000) (1738633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35561728 :
    ThetaLowerSegment 35561728 35578112 (3555214351857 / 100000) (711364177881 / 20000) := by
  exact
    packedTile8192 35561728 35578112 11 924 5963 25 _ _ (1738677 / 100000) (43467 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35578112 :
    ThetaLowerSegment 35578112 35594496 (711364177881 / 20000) (889610779491 / 25000) := by
  exact
    packedTile8192 35578112 35594496 11 933 5964 25 _ _ (1738723 / 100000) (869363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35594496 :
    ThetaLowerSegment 35594496 35610880 (889610779491 / 25000) (3560082777131 / 100000) := by
  exact
    packedTile8192 35594496 35610880 11 943 5966 25 _ _ (1738769 / 100000) (434693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35610880 :
    ThetaLowerSegment 35610880 35627264 (3560082777131 / 100000) (3561717263231 / 100000) := by
  exact
    packedTile8192 35610880 35627264 11 940 5967 25 _ _ (347763 / 20000) (869409 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35627264 :
    ThetaLowerSegment 35627264 35643648 (3561717263231 / 100000) (3563386569791 / 100000) := by
  exact
    packedTile8192 35627264 35643648 11 960 5968 25 _ _ (1738861 / 100000) (108679 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35643648 :
    ThetaLowerSegment 35643648 35660032 (3563386569791 / 100000) (1782511440639 / 50000) := by
  exact
    packedTile8192 35643648 35660032 11 941 5970 25 _ _ (1738907 / 100000) (173891 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35660032 :
    ThetaLowerSegment 35660032 35676416 (1782511440639 / 50000) (891668721657 / 25000) := by
  exact
    packedTile8192 35660032 35676416 11 950 5971 25 _ _ (1738953 / 100000) (434739 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35676416 :
    ThetaLowerSegment 35676416 35692800 (891668721657 / 25000) (1784156511843 / 50000) := by
  exact
    packedTile8192 35676416 35692800 11 942 5972 25 _ _ (1738999 / 100000) (869501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35692800 :
    ThetaLowerSegment 35692800 35709184 (1784156511843 / 50000) (1784959950171 / 50000) := by
  exact
    packedTile8192 35692800 35709184 11 924 5974 25 _ _ (434761 / 25000) (1739047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35709184 :
    ThetaLowerSegment 35709184 35725568 (1784959950171 / 50000) (1785763409751 / 50000) := by
  exact
    packedTile8192 35709184 35725568 11 924 5975 25 _ _ (173909 / 10000) (1739093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35725568 :
    ThetaLowerSegment 35725568 35741952 (1785763409751 / 50000) (1786599064599 / 50000) := by
  exact
    packedTile8192 35725568 35741952 11 961 5977 25 _ _ (54348 / 3125) (1739139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35741952 :
    ThetaLowerSegment 35741952 35758336 (1786599064599 / 50000) (1787425176049 / 50000) := by
  exact
    packedTile8192 35741952 35758336 11 950 5978 25 _ _ (869591 / 50000) (347837 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35758336 :
    ThetaLowerSegment 35758336 35774720 (1787425176049 / 50000) (1788253048577 / 50000) := by
  exact
    packedTile8192 35758336 35774720 11 952 5979 25 _ _ (434807 / 25000) (1739231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35774720 :
    ThetaLowerSegment 35774720 35791104 (1788253048577 / 50000) (894544384867 / 25000) := by
  exact
    packedTile8192 35774720 35791104 11 961 5981 25 _ _ (869637 / 50000) (1739277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35791104 :
    ThetaLowerSegment 35791104 35807488 (894544384867 / 25000) (111869140604 / 3125) := by
  exact
    packedTile8192 35791104 35807488 11 940 5982 25 _ _ (1739319 / 100000) (869661 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35807488 :
    ThetaLowerSegment 35807488 35823872 (111869140604 / 3125) (3581397060843 / 100000) := by
  exact
    packedTile8192 35807488 35823872 11 911 5983 25 _ _ (347873 / 20000) (217421 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35823872 :
    ThetaLowerSegment 35823872 35840256 (3581397060843 / 100000) (1791534317407 / 50000) := by
  exact
    packedTile8192 35823872 35840256 11 961 5985 25 _ _ (1739411 / 100000) (869707 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35840256 :
    ThetaLowerSegment 35840256 35856640 (1791534317407 / 50000) (224044635071 / 6250) := by
  exact
    packedTile8192 35840256 35856640 11 946 5986 25 _ _ (1739457 / 100000) (86973 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35856640 :
    ThetaLowerSegment 35856640 35873024 (224044635071 / 6250) (448288443121 / 12500) := by
  exact
    packedTile8192 35856640 35873024 11 916 5988 25 _ _ (869751 / 50000) (347901 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35873024 :
    ThetaLowerSegment 35873024 35889408 (448288443121 / 12500) (224244028127 / 6250) := by
  exact
    packedTile8192 35873024 35889408 11 918 5989 25 _ _ (434887 / 25000) (1739551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35889408 :
    ThetaLowerSegment 35889408 35905792 (224244028127 / 6250) (224344924579 / 6250) := by
  exact
    packedTile8192 35889408 35905792 11 928 5990 25 _ _ (869797 / 50000) (1739597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35905792 :
    ThetaLowerSegment 35905792 35922176 (224344924579 / 6250) (897788513481 / 25000) := by
  exact
    packedTile8192 35905792 35922176 11 940 5992 25 _ _ (1739639 / 100000) (869821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35922176 :
    ThetaLowerSegment 35922176 35938560 (897788513481 / 25000) (3592815453099 / 100000) := by
  exact
    packedTile8192 35922176 35938560 11 955 5993 25 _ _ (347937 / 20000) (217461 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35938560 :
    ThetaLowerSegment 35938560 35954944 (3592815453099 / 100000) (3594447320777 / 100000) := by
  exact
    packedTile8192 35938560 35954944 11 938 5994 25 _ _ (1739731 / 100000) (869867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35954944 :
    ThetaLowerSegment 35954944 35971328 (3594447320777 / 100000) (3596058353353 / 100000) := by
  exact
    packedTile8192 35954944 35971328 11 926 5996 25 _ _ (54368 / 3125) (1739779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35971328 :
    ThetaLowerSegment 35971328 35987712 (3596058353353 / 100000) (3597697265677 / 100000) := by
  exact
    packedTile8192 35971328 35987712 11 942 5997 25 _ _ (869911 / 50000) (69593 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell35987712 :
    ThetaLowerSegment 35987712 36004096 (3597697265677 / 100000) (3599371017731 / 100000) := by
  exact
    packedTile8192 35987712 36004096 11 962 5998 25 _ _ (1739867 / 100000) (173987 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36004096 :
    ThetaLowerSegment 36004096 36020480 (3599371017731 / 100000) (720211050703 / 20000) := by
  exact
    packedTile8192 36004096 36020480 11 968 6000 25 _ _ (1739913 / 100000) (434979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36020480 :
    ThetaLowerSegment 36020480 36036864 (720211050703 / 20000) (3602720393321 / 100000) := by
  exact
    packedTile8192 36020480 36036864 11 957 6001 25 _ _ (869979 / 50000) (1739961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36036864 :
    ThetaLowerSegment 36036864 36053248 (3602720393321 / 100000) (3604315976989 / 100000) := by
  exact
    packedTile8192 36036864 36053248 11 917 6003 25 _ _ (435001 / 25000) (1740007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36053248 :
    ThetaLowerSegment 36053248 36069632 (3604315976989 / 100000) (3605927262363 / 100000) := by
  exact
    packedTile8192 36053248 36069632 11 926 6004 25 _ _ (1740049 / 100000) (435013 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36069632 :
    ThetaLowerSegment 36069632 36086016 (3605927262363 / 100000) (3607583832803 / 100000) := by
  exact
    packedTile8192 36069632 36086016 11 952 6005 25 _ _ (348019 / 20000) (870049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36086016 :
    ThetaLowerSegment 36086016 36102400 (3607583832803 / 100000) (3609249146783 / 100000) := by
  exact
    packedTile8192 36086016 36102400 11 957 6007 25 _ _ (87007 / 5000) (1740143 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36102400 :
    ThetaLowerSegment 36102400 36118784 (3609249146783 / 100000) (1805448550989 / 50000) := by
  exact
    packedTile8192 36102400 36118784 11 947 6008 25 _ _ (348037 / 20000) (435047 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36118784 :
    ThetaLowerSegment 36118784 36135168 (1805448550989 / 50000) (1806262979097 / 50000) := by
  exact
    packedTile8192 36118784 36135168 11 936 6009 25 _ _ (1740231 / 100000) (870117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36135168 :
    ThetaLowerSegment 36135168 36151552 (1806262979097 / 50000) (1807093090749 / 50000) := by
  exact
    packedTile8192 36135168 36151552 11 954 6011 25 _ _ (435069 / 25000) (1740279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36151552 :
    ThetaLowerSegment 36151552 36167936 (1807093090749 / 50000) (180787710581 / 5000) := by
  exact
    packedTile8192 36151552 36167936 11 901 6012 25 _ _ (870161 / 50000) (69613 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36167936 :
    ThetaLowerSegment 36167936 36184320 (180787710581 / 5000) (723476290953 / 20000) := by
  exact
    packedTile8192 36167936 36184320 11 935 6013 25 _ _ (1740367 / 100000) (174037 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36184320 :
    ThetaLowerSegment 36184320 36200704 (723476290953 / 20000) (3619010480397 / 100000) := by
  exact
    packedTile8192 36184320 36200704 11 936 6015 25 _ _ (435103 / 25000) (348083 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36200704 :
    ThetaLowerSegment 36200704 36217088 (3619010480397 / 100000) (1810320644303 / 50000) := by
  exact
    packedTile8192 36200704 36217088 11 937 6016 25 _ _ (1740457 / 100000) (87023 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36217088 :
    ThetaLowerSegment 36217088 36233472 (1810320644303 / 50000) (45278858631 / 1250) := by
  exact
    packedTile8192 36217088 36233472 11 958 6018 25 _ _ (1740503 / 100000) (870253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36233472 :
    ThetaLowerSegment 36233472 36249856 (45278858631 / 1250) (226496115213 / 6250) := by
  exact
    packedTile8192 36233472 36249856 11 936 6019 25 _ _ (435137 / 25000) (1740551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36249856 :
    ThetaLowerSegment 36249856 36266240 (226496115213 / 6250) (453202842179 / 12500) := by
  exact
    packedTile8192 36249856 36266240 11 968 6020 25 _ _ (1740593 / 100000) (435149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36266240 :
    ThetaLowerSegment 36266240 36282624 (453202842179 / 12500) (226704553891 / 6250) := by
  exact
    packedTile8192 36266240 36282624 11 948 6022 25 _ _ (870319 / 50000) (1740641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36282624 :
    ThetaLowerSegment 36282624 36299008 (226704553891 / 6250) (907244682899 / 25000) := by
  exact
    packedTile8192 36282624 36299008 11 980 6023 25 _ _ (1740683 / 100000) (870343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36299008 :
    ThetaLowerSegment 36299008 36315392 (907244682899 / 25000) (1815274434577 / 50000) := by
  exact
    packedTile8192 36299008 36315392 11 902 6024 25 _ _ (1740729 / 100000) (435183 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36315392 :
    ThetaLowerSegment 36315392 36331776 (1815274434577 / 50000) (1816123932289 / 50000) := by
  exact
    packedTile8192 36315392 36331776 11 976 6026 25 _ _ (870387 / 50000) (1740777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36331776 :
    ThetaLowerSegment 36331776 36348160 (1816123932289 / 50000) (3633920791637 / 100000) := by
  exact
    packedTile8192 36331776 36348160 11 961 6027 25 _ _ (1740819 / 100000) (870411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36348160 :
    ThetaLowerSegment 36348160 36364544 (3633920791637 / 100000) (3635548499477 / 100000) := by
  exact
    packedTile8192 36348160 36364544 11 935 6028 25 _ _ (54402 / 3125) (1740867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36364544 :
    ThetaLowerSegment 36364544 36380928 (3635548499477 / 100000) (363717973121 / 10000) := by
  exact
    packedTile8192 36364544 36380928 11 937 6030 25 _ _ (1740909 / 100000) (108807 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36380928 :
    ThetaLowerSegment 36380928 36397312 (363717973121 / 10000) (909694046507 / 25000) := by
  exact
    packedTile8192 36380928 36397312 11 917 6031 25 _ _ (870477 / 50000) (1740957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36397312 :
    ThetaLowerSegment 36397312 36413696 (909694046507 / 25000) (910104922271 / 25000) := by
  exact
    packedTile8192 36397312 36413696 11 944 6033 25 _ _ (1740999 / 100000) (870501 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36413696 :
    ThetaLowerSegment 36413696 36430080 (910104922271 / 25000) (455253334087 / 12500) := by
  exact
    packedTile8192 36413696 36430080 11 923 6034 25 _ _ (435261 / 25000) (1741047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36430080 :
    ThetaLowerSegment 36430080 36446464 (455253334087 / 12500) (364367374289 / 10000) := by
  exact
    packedTile8192 36430080 36446464 11 946 6035 25 _ _ (1741089 / 100000) (435273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36446464 :
    ThetaLowerSegment 36446464 36462848 (364367374289 / 10000) (72906208177 / 2000) := by
  exact
    packedTile8192 36446464 36462848 11 940 6037 25 _ _ (870567 / 50000) (1741137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36462848 :
    ThetaLowerSegment 36462848 36479232 (72906208177 / 2000) (911748096941 / 25000) := by
  exact
    packedTile8192 36462848 36479232 11 966 6038 25 _ _ (1741179 / 100000) (870591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36479232 :
    ThetaLowerSegment 36479232 36495616 (911748096941 / 25000) (912162943559 / 25000) := by
  exact
    packedTile8192 36479232 36495616 11 953 6039 25 _ _ (217653 / 12500) (1741227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36495616 :
    ThetaLowerSegment 36495616 36512000 (912162943559 / 25000) (3650241552833 / 100000) := by
  exact
    packedTile8192 36495616 36512000 11 913 6041 25 _ _ (1741269 / 100000) (217659 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36512000 :
    ThetaLowerSegment 36512000 36528384 (3650241552833 / 100000) (3651873164051 / 100000) := by
  exact
    packedTile8192 36512000 36528384 11 937 6042 25 _ _ (870657 / 50000) (1741317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36528384 :
    ThetaLowerSegment 36528384 36544768 (3651873164051 / 100000) (1826759374153 / 50000) := by
  exact
    packedTile8192 36528384 36544768 11 945 6043 25 _ _ (1741359 / 100000) (870681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36544768 :
    ThetaLowerSegment 36544768 36561152 (1826759374153 / 50000) (22844701152 / 625) := by
  exact
    packedTile8192 36544768 36561152 11 938 6045 25 _ _ (1741403 / 100000) (870703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36561152 :
    ThetaLowerSegment 36561152 36577536 (22844701152 / 625) (91419075593 / 2500) := by
  exact
    packedTile8192 36561152 36577536 11 925 6046 25 _ _ (217681 / 12500) (1741451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36577536 :
    ThetaLowerSegment 36577536 36593920 (91419075593 / 2500) (731692195879 / 20000) := by
  exact
    packedTile8192 36577536 36593920 11 975 6047 25 _ _ (1741493 / 100000) (217687 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36593920 :
    ThetaLowerSegment 36593920 36610304 (731692195879 / 20000) (732019605023 / 20000) := by
  exact
    packedTile8192 36593920 36610304 11 940 6049 25 _ _ (870769 / 50000) (1741541 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36610304 :
    ThetaLowerSegment 36610304 36626688 (732019605023 / 20000) (3661731629969 / 100000) := by
  exact
    packedTile8192 36610304 36626688 11 938 6050 25 _ _ (1741583 / 100000) (870793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36626688 :
    ThetaLowerSegment 36626688 36643072 (3661731629969 / 100000) (114479457342 / 3125) := by
  exact
    packedTile8192 36626688 36643072 11 925 6051 25 _ _ (1741627 / 100000) (174163 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36643072 :
    ThetaLowerSegment 36643072 36659456 (114479457342 / 3125) (91625061209 / 2500) := by
  exact
    packedTile8192 36643072 36659456 11 953 6053 25 _ _ (217709 / 12500) (69667 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36659456 :
    ThetaLowerSegment 36659456 36675840 (91625061209 / 2500) (3666603086283 / 100000) := by
  exact
    packedTile8192 36659456 36675840 11 919 6054 25 _ _ (1741717 / 100000) (43543 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36675840 :
    ThetaLowerSegment 36675840 36692224 (3666603086283 / 100000) (22926251757 / 625) := by
  exact
    packedTile8192 36675840 36692224 11 917 6056 25 _ _ (1741761 / 100000) (435441 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36692224 :
    ThetaLowerSegment 36692224 36708608 (22926251757 / 625) (1834912693059 / 50000) := by
  exact
    packedTile8192 36692224 36708608 11 933 6057 25 _ _ (870903 / 50000) (1741809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36708608 :
    ThetaLowerSegment 36708608 36724992 (1834912693059 / 50000) (1835710460817 / 50000) := by
  exact
    packedTile8192 36708608 36724992 11 916 6058 25 _ _ (1741851 / 100000) (870927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36724992 :
    ThetaLowerSegment 36724992 36741376 (1835710460817 / 50000) (918261962891 / 25000) := by
  exact
    packedTile8192 36724992 36741376 11 934 6060 25 _ _ (348379 / 20000) (870949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36741376 :
    ThetaLowerSegment 36741376 36757760 (918261962891 / 25000) (114835928967 / 3125) := by
  exact
    packedTile8192 36741376 36757760 11 977 6061 25 _ _ (87097 / 5000) (1741943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36757760 :
    ThetaLowerSegment 36757760 36774144 (114835928967 / 3125) (22977681247 / 625) := by
  exact
    packedTile8192 36757760 36774144 11 964 6062 25 _ _ (54437 / 3125) (1741987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36774144 :
    ThetaLowerSegment 36774144 36790528 (22977681247 / 625) (3678054312577 / 100000) := by
  exact
    packedTile8192 36774144 36790528 11 933 6064 25 _ _ (1742029 / 100000) (108877 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36790528 :
    ThetaLowerSegment 36790528 36806912 (3678054312577 / 100000) (3679679667619 / 100000) := by
  exact
    packedTile8192 36790528 36806912 11 933 6065 25 _ _ (871037 / 50000) (1742077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36806912 :
    ThetaLowerSegment 36806912 36823296 (3679679667619 / 100000) (3681383459023 / 100000) := by
  exact
    packedTile8192 36806912 36823296 11 978 6066 25 _ _ (871059 / 50000) (1742121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36823296 :
    ThetaLowerSegment 36823296 36839680 (3681383459023 / 100000) (736577737571 / 20000) := by
  exact
    packedTile8192 36823296 36839680 11 864 6068 25 _ _ (1742163 / 100000) (871083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36839680 :
    ThetaLowerSegment 36839680 36856064 (736577737571 / 20000) (3684550753333 / 100000) := by
  exact
    packedTile8192 36839680 36856064 11 954 6069 25 _ _ (1742207 / 100000) (174221 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36856064 :
    ThetaLowerSegment 36856064 36872448 (3684550753333 / 100000) (3686195439221 / 100000) := by
  exact
    packedTile8192 36856064 36872448 11 944 6070 25 _ _ (435563 / 25000) (348451 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36872448 :
    ThetaLowerSegment 36872448 36888832 (3686195439221 / 100000) (737559321849 / 20000) := by
  exact
    packedTile8192 36872448 36888832 11 919 6072 25 _ _ (217787 / 12500) (1742299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36888832 :
    ThetaLowerSegment 36888832 36905216 (737559321849 / 20000) (737871200709 / 20000) := by
  exact
    packedTile8192 36888832 36905216 11 895 6073 25 _ _ (87117 / 5000) (1742343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36905216 :
    ThetaLowerSegment 36905216 36921600 (737871200709 / 20000) (369095377059 / 10000) := by
  exact
    packedTile8192 36905216 36921600 11 917 6074 25 _ _ (348477 / 20000) (435597 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36921600 :
    ThetaLowerSegment 36921600 36937984 (369095377059 / 10000) (230788502991 / 6250) := by
  exact
    packedTile8192 36921600 36937984 11 954 6076 25 _ _ (1742429 / 100000) (54451 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36937984 :
    ThetaLowerSegment 36937984 36954368 (230788502991 / 6250) (1847129600419 / 50000) := by
  exact
    packedTile8192 36937984 36954368 11 943 6077 25 _ _ (871237 / 50000) (1742477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36954368 :
    ThetaLowerSegment 36954368 36970752 (1847129600419 / 50000) (1847962524023 / 50000) := by
  exact
    packedTile8192 36954368 36970752 11 956 6079 25 _ _ (871259 / 50000) (1742521 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36970752 :
    ThetaLowerSegment 36970752 36987136 (1847962524023 / 50000) (115549553426 / 3125) := by
  exact
    packedTile8192 36970752 36987136 11 953 6080 25 _ _ (871281 / 50000) (348513 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell36987136 :
    ThetaLowerSegment 36987136 37003520 (115549553426 / 3125) (739844403521 / 20000) := by
  exact
    packedTile8192 36987136 37003520 11 939 6081 25 _ _ (1742607 / 100000) (174261 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37003520 :
    ThetaLowerSegment 37003520 37019904 (739844403521 / 20000) (740178992513 / 20000) := by
  exact
    packedTile8192 37003520 37019904 11 960 6083 25 _ _ (1742651 / 100000) (871327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37019904 :
    ThetaLowerSegment 37019904 37036288 (740178992513 / 20000) (148101881497 / 4000) := by
  exact
    packedTile8192 37019904 37036288 11 948 6084 25 _ _ (348539 / 20000) (871349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37036288 :
    ThetaLowerSegment 37036288 37052672 (148101881497 / 4000) (3704171270173 / 100000) := by
  exact
    packedTile8192 37036288 37052672 11 932 6085 25 _ _ (1742739 / 100000) (871371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37052672 :
    ThetaLowerSegment 37052672 37069056 (3704171270173 / 100000) (3705809487133 / 100000) := by
  exact
    packedTile8192 37052672 37069056 11 940 6087 25 _ _ (54462 / 3125) (1742787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37069056 :
    ThetaLowerSegment 37069056 37085440 (3705809487133 / 100000) (29659568021 / 800) := by
  exact
    packedTile8192 37069056 37085440 11 939 6088 25 _ _ (435707 / 25000) (1742831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37085440 :
    ThetaLowerSegment 37085440 37101824 (29659568021 / 800) (3709099988153 / 100000) := by
  exact
    packedTile8192 37085440 37101824 11 949 6089 25 _ _ (217859 / 12500) (13943 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37101824 :
    ThetaLowerSegment 37101824 37118208 (3709099988153 / 100000) (3710813274581 / 100000) := by
  exact
    packedTile8192 37101824 37118208 11 983 6091 25 _ _ (435729 / 25000) (1742919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37118208 :
    ThetaLowerSegment 37118208 37134592 (3710813274581 / 100000) (3712498716901 / 100000) := by
  exact
    packedTile8192 37118208 37134592 11 967 6092 25 _ _ (21787 / 1250) (1742963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37134592 :
    ThetaLowerSegment 37134592 37150976 (3712498716901 / 100000) (3714166771729 / 100000) := by
  exact
    packedTile8192 37134592 37150976 11 957 6093 25 _ _ (435751 / 25000) (1743007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37150976 :
    ThetaLowerSegment 37150976 37167360 (3714166771729 / 100000) (928943901489 / 25000) := by
  exact
    packedTile8192 37150976 37167360 11 923 6095 25 _ _ (1743049 / 100000) (435763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37167360 :
    ThetaLowerSegment 37167360 37183744 (928943901489 / 25000) (3717415856469 / 100000) := by
  exact
    packedTile8192 37167360 37183744 11 941 6096 25 _ _ (1743093 / 100000) (217887 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37183744 :
    ThetaLowerSegment 37183744 37200128 (3717415856469 / 100000) (3719040460153 / 100000) := by
  exact
    packedTile8192 37183744 37200128 11 932 6097 25 _ _ (1743137 / 100000) (87157 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37200128 :
    ThetaLowerSegment 37200128 37216512 (3719040460153 / 100000) (1860350855823 / 50000) := by
  exact
    packedTile8192 37200128 37216512 11 953 6099 25 _ _ (1743181 / 100000) (108949 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37216512 :
    ThetaLowerSegment 37216512 37232896 (1860350855823 / 50000) (3722268870921 / 100000) := by
  exact
    packedTile8192 37216512 37232896 11 899 6100 25 _ _ (69729 / 4000) (435807 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37232896 :
    ThetaLowerSegment 37232896 37249280 (3722268870921 / 100000) (186196335987 / 5000) := by
  exact
    packedTile8192 37232896 37249280 11 951 6101 25 _ _ (1743269 / 100000) (217909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37249280 :
    ThetaLowerSegment 37249280 37265664 (186196335987 / 5000) (3725500931379 / 100000) := by
  exact
    packedTile8192 37249280 37265664 11 903 6103 25 _ _ (1743313 / 100000) (435829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37265664 :
    ThetaLowerSegment 37265664 37282048 (3725500931379 / 100000) (372714491703 / 10000) := by
  exact
    packedTile8192 37265664 37282048 11 943 6104 25 _ _ (1743357 / 100000) (10896 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37282048 :
    ThetaLowerSegment 37282048 37298432 (372714491703 / 10000) (932186339787 / 25000) := by
  exact
    packedTile8192 37282048 37298432 11 918 6105 25 _ _ (1743401 / 100000) (435851 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37298432 :
    ThetaLowerSegment 37298432 37314816 (932186339787 / 25000) (932604766587 / 25000) := by
  exact
    packedTile8192 37298432 37314816 11 960 6107 25 _ _ (348689 / 20000) (217931 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37314816 :
    ThetaLowerSegment 37314816 37331200 (932604766587 / 25000) (1866013281603 / 50000) := by
  exact
    packedTile8192 37314816 37331200 11 922 6108 25 _ _ (1743489 / 100000) (435873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37331200 :
    ThetaLowerSegment 37331200 37347584 (1866013281603 / 50000) (1866828382813 / 50000) := by
  exact
    packedTile8192 37331200 37347584 11 935 6109 25 _ _ (435883 / 25000) (348707 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37347584 :
    ThetaLowerSegment 37347584 37363968 (1866828382813 / 50000) (1867676632537 / 50000) := by
  exact
    packedTile8192 37347584 37363968 11 973 6111 25 _ _ (217947 / 12500) (1743579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37363968 :
    ThetaLowerSegment 37363968 37380352 (1867676632537 / 50000) (1868481313167 / 50000) := by
  exact
    packedTile8192 37363968 37380352 11 923 6112 25 _ _ (87181 / 5000) (1743623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37380352 :
    ThetaLowerSegment 37380352 37396736 (1868481313167 / 50000) (1869320015551 / 50000) := by
  exact
    packedTile8192 37380352 37396736 11 962 6113 25 _ _ (108979 / 6250) (1743667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37396736 :
    ThetaLowerSegment 37396736 37413120 (1869320015551 / 50000) (74806140319 / 2000) := by
  exact
    packedTile8192 37396736 37413120 11 956 6115 25 _ _ (435927 / 25000) (1743711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37413120 :
    ThetaLowerSegment 37413120 37429504 (74806140319 / 2000) (1870949530763 / 50000) := by
  exact
    packedTile8192 37413120 37429504 11 913 6116 25 _ _ (217969 / 12500) (348751 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37429504 :
    ThetaLowerSegment 37429504 37445888 (1870949530763 / 50000) (1871744701283 / 50000) := by
  exact
    packedTile8192 37429504 37445888 11 912 6117 25 _ _ (348759 / 20000) (871899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37445888 :
    ThetaLowerSegment 37445888 37462272 (1871744701283 / 50000) (3745116404353 / 100000) := by
  exact
    packedTile8192 37445888 37462272 11 933 6119 25 _ _ (1743839 / 100000) (871921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37462272 :
    ThetaLowerSegment 37462272 37478656 (3745116404353 / 100000) (1873390906309 / 50000) := by
  exact
    packedTile8192 37462272 37478656 11 955 6120 25 _ _ (1743883 / 100000) (871943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37478656 :
    ThetaLowerSegment 37478656 37495040 (1873390906309 / 50000) (749691545293 / 20000) := by
  exact
    packedTile8192 37478656 37495040 11 961 6121 25 _ _ (1743927 / 100000) (174393 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37495040 :
    ThetaLowerSegment 37495040 37511424 (749691545293 / 20000) (30000957839 / 800) := by
  exact
    packedTile8192 37495040 37511424 11 953 6123 25 _ _ (174397 / 10000) (1743973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37511424 :
    ThetaLowerSegment 37511424 37527808 (30000957839 / 800) (3751764335077 / 100000) := by
  exact
    packedTile8192 37511424 37527808 11 943 6124 25 _ _ (872007 / 50000) (1744017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37527808 :
    ThetaLowerSegment 37527808 37544192 (3751764335077 / 100000) (3753456071337 / 100000) := by
  exact
    packedTile8192 37527808 37544192 11 970 6125 25 _ _ (872029 / 50000) (1744061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37544192 :
    ThetaLowerSegment 37544192 37560576 (3753456071337 / 100000) (3755071108863 / 100000) := by
  exact
    packedTile8192 37544192 37560576 11 926 6127 25 _ _ (1744101 / 100000) (218013 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37560576 :
    ThetaLowerSegment 37560576 37576960 (3755071108863 / 100000) (3756668745683 / 100000) := by
  exact
    packedTile8192 37560576 37576960 11 916 6128 25 _ _ (348829 / 20000) (436037 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37576960 :
    ThetaLowerSegment 37576960 37593344 (3756668745683 / 100000) (375827863213 / 10000) := by
  exact
    packedTile8192 37576960 37593344 11 923 6130 25 _ _ (1744189 / 100000) (54506 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37593344 :
    ThetaLowerSegment 37593344 37609728 (375827863213 / 10000) (1879947767597 / 50000) := by
  exact
    packedTile8192 37593344 37609728 11 927 6131 25 _ _ (218029 / 12500) (348847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37609728 :
    ThetaLowerSegment 37609728 37626112 (1879947767597 / 50000) (376159794857 / 10000) := by
  exact
    packedTile8192 37609728 37626112 11 976 6132 25 _ _ (436069 / 25000) (1744279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37626112 :
    ThetaLowerSegment 37626112 37642496 (376159794857 / 10000) (150529853201 / 4000) := by
  exact
    packedTile8192 37626112 37642496 11 945 6134 25 _ _ (1744319 / 100000) (872161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37642496 :
    ThetaLowerSegment 37642496 37658880 (150529853201 / 4000) (376484242217 / 10000) := by
  exact
    packedTile8192 37642496 37658880 11 915 6135 25 _ _ (1744363 / 100000) (872183 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37658880 :
    ThetaLowerSegment 37658880 37675264 (376484242217 / 10000) (1883281203243 / 50000) := by
  exact
    packedTile8192 37658880 37675264 11 986 6136 25 _ _ (872203 / 50000) (1744409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37675264 :
    ThetaLowerSegment 37675264 37691648 (1883281203243 / 50000) (942037900109 / 25000) := by
  exact
    packedTile8192 37675264 37691648 11 911 6138 25 _ _ (34889 / 2000) (1744453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37691648 :
    ThetaLowerSegment 37691648 37708032 (942037900109 / 25000) (3769775723419 / 100000) := by
  exact
    packedTile8192 37691648 37708032 11 931 6139 25 _ _ (1744493 / 100000) (109031 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37708032 :
    ThetaLowerSegment 37708032 37724416 (3769775723419 / 100000) (3771436522643 / 100000) := by
  exact
    packedTile8192 37708032 37724416 11 952 6140 25 _ _ (1744537 / 100000) (87227 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37724416 :
    ThetaLowerSegment 37724416 37740800 (3771436522643 / 100000) (3773060726623 / 100000) := by
  exact
    packedTile8192 37724416 37740800 11 931 6142 25 _ _ (87229 / 5000) (1744583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37740800 :
    ThetaLowerSegment 37740800 37757184 (3773060726623 / 100000) (3774709396303 / 100000) := by
  exact
    packedTile8192 37740800 37757184 11 945 6143 25 _ _ (109039 / 6250) (1744627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37757184 :
    ThetaLowerSegment 37757184 37773568 (3774709396303 / 100000) (944085164987 / 25000) := by
  exact
    packedTile8192 37757184 37773568 11 935 6144 25 _ _ (1744667 / 100000) (174467 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37773568 :
    ThetaLowerSegment 37773568 37789952 (944085164987 / 25000) (3777964985889 / 100000) := by
  exact
    packedTile8192 37773568 37789952 11 931 6146 25 _ _ (1744711 / 100000) (872357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37789952 :
    ThetaLowerSegment 37789952 37806336 (3777964985889 / 100000) (3779575393831 / 100000) := by
  exact
    packedTile8192 37789952 37806336 11 923 6147 25 _ _ (872377 / 50000) (1744757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37806336 :
    ThetaLowerSegment 37806336 37822720 (3779575393831 / 100000) (756236819333 / 20000) := by
  exact
    packedTile8192 37806336 37822720 11 922 6148 25 _ _ (1744797 / 100000) (2181 / 125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37822720 :
    ThetaLowerSegment 37822720 37839104 (756236819333 / 20000) (3782883571799 / 100000) := by
  exact
    packedTile8192 37822720 37839104 11 974 6150 25 _ _ (1744841 / 100000) (436211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37839104 :
    ThetaLowerSegment 37839104 37855488 (3782883571799 / 100000) (756902658691 / 20000) := by
  exact
    packedTile8192 37839104 37855488 11 934 6151 25 _ _ (436221 / 25000) (1744887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37855488 :
    ThetaLowerSegment 37855488 37871872 (756902658691 / 20000) (3786108156733 / 100000) := by
  exact
    packedTile8192 37855488 37871872 11 914 6152 25 _ _ (1744927 / 100000) (174493 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37871872 :
    ThetaLowerSegment 37871872 37888256 (3786108156733 / 100000) (3787725743923 / 100000) := by
  exact
    packedTile8192 37871872 37888256 11 927 6154 25 _ _ (174497 / 10000) (1744973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37888256 :
    ThetaLowerSegment 37888256 37904640 (3787725743923 / 100000) (3789383507223 / 100000) := by
  exact
    packedTile8192 37888256 37904640 11 950 6155 25 _ _ (872507 / 50000) (1745017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37904640 :
    ThetaLowerSegment 37904640 37921024 (3789383507223 / 100000) (3791006410233 / 100000) := by
  exact
    packedTile8192 37904640 37921024 11 930 6156 25 _ _ (1745057 / 100000) (87253 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37921024 :
    ThetaLowerSegment 37921024 37937408 (3791006410233 / 100000) (3792676470933 / 100000) := by
  exact
    packedTile8192 37921024 37937408 11 957 6158 25 _ _ (17451 / 1000) (1745103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37937408 :
    ThetaLowerSegment 37937408 37953792 (3792676470933 / 100000) (237139680227 / 6250) := by
  exact
    packedTile8192 37937408 37953792 11 893 6159 25 _ _ (1745143 / 100000) (872573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37953792 :
    ThetaLowerSegment 37953792 37970176 (237139680227 / 6250) (1897962984433 / 50000) := by
  exact
    packedTile8192 37953792 37970176 11 969 6160 25 _ _ (872593 / 50000) (1745189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37970176 :
    ThetaLowerSegment 37970176 37986560 (1897962984433 / 50000) (1898764045003 / 50000) := by
  exact
    packedTile8192 37970176 37986560 11 918 6161 25 _ _ (174523 / 10000) (1745233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell37986560 :
    ThetaLowerSegment 37986560 38002944 (1898764045003 / 50000) (3799177372991 / 100000) := by
  exact
    packedTile8192 37986560 38002944 11 945 6163 25 _ _ (1745273 / 100000) (436319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38002944 :
    ThetaLowerSegment 38002944 38019328 (3799177372991 / 100000) (3800821460663 / 100000) := by
  exact
    packedTile8192 38002944 38019328 11 942 6164 25 _ _ (436329 / 25000) (1745319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38019328 :
    ThetaLowerSegment 38019328 38035712 (3800821460663 / 100000) (1901214468151 / 50000) := by
  exact
    packedTile8192 38019328 38035712 11 921 6165 25 _ _ (1745359 / 100000) (872681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38035712 :
    ThetaLowerSegment 38035712 38052096 (1901214468151 / 50000) (380411150383 / 10000) := by
  exact
    packedTile8192 38035712 38052096 11 964 6167 25 _ _ (872701 / 50000) (349081 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38052096 :
    ThetaLowerSegment 38052096 38068480 (380411150383 / 10000) (761153586227 / 20000) := by
  exact
    packedTile8192 38052096 38068480 11 949 6168 25 _ _ (349089 / 20000) (218181 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38068480 :
    ThetaLowerSegment 38068480 38084864 (761153586227 / 20000) (3807480254863 / 100000) := by
  exact
    packedTile8192 38068480 38084864 11 981 6169 25 _ _ (109093 / 6250) (1745491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38084864 :
    ThetaLowerSegment 38084864 38101248 (3807480254863 / 100000) (3809065197011 / 100000) := by
  exact
    packedTile8192 38084864 38101248 11 908 6171 25 _ _ (1745531 / 100000) (872767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38101248 :
    ThetaLowerSegment 38101248 38117632 (3809065197011 / 100000) (3810720001163 / 100000) := by
  exact
    packedTile8192 38101248 38117632 11 948 6172 25 _ _ (872787 / 50000) (1745577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38117632 :
    ThetaLowerSegment 38117632 38134016 (3810720001163 / 100000) (953085419839 / 25000) := by
  exact
    packedTile8192 38117632 38134016 11 929 6173 25 _ _ (1745617 / 100000) (87281 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38134016 :
    ThetaLowerSegment 38134016 38150400 (953085419839 / 25000) (953504378239 / 25000) := by
  exact
    packedTile8192 38134016 38150400 11 960 6175 25 _ _ (87283 / 5000) (1745663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38150400 :
    ThetaLowerSegment 38150400 38166784 (953504378239 / 25000) (1907817016967 / 50000) := by
  exact
    packedTile8192 38150400 38166784 11 926 6176 25 _ _ (1745703 / 100000) (872853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38166784 :
    ThetaLowerSegment 38166784 38183168 (1907817016967 / 50000) (477170072091 / 12500) := by
  exact
    packedTile8192 38166784 38183168 11 989 6177 25 _ _ (872873 / 50000) (1745749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38183168 :
    ThetaLowerSegment 38183168 38199552 (477170072091 / 12500) (152758877599 / 4000) := by
  exact
    packedTile8192 38183168 38199552 11 923 6179 25 _ _ (1745789 / 100000) (54556 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38199552 :
    ThetaLowerSegment 38199552 38215936 (152758877599 / 4000) (3820620005383 / 100000) := by
  exact
    packedTile8192 38199552 38215936 11 944 6180 25 _ _ (218229 / 12500) (349167 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38215936 :
    ThetaLowerSegment 38215936 38232320 (3820620005383 / 100000) (3822243669133 / 100000) := by
  exact
    packedTile8192 38215936 38232320 11 930 6181 25 _ _ (13967 / 800) (872939 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38232320 :
    ThetaLowerSegment 38232320 38248704 (3822243669133 / 100000) (3823877848381 / 100000) := by
  exact
    packedTile8192 38232320 38248704 11 936 6183 25 _ _ (872959 / 50000) (1745921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38248704 :
    ThetaLowerSegment 38248704 38265088 (3823877848381 / 100000) (3825564446707 / 100000) := by
  exact
    packedTile8192 38248704 38265088 11 966 6184 25 _ _ (1745961 / 100000) (436491 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38265088 :
    ThetaLowerSegment 38265088 38281472 (3825564446707 / 100000) (3827202197521 / 100000) := by
  exact
    packedTile8192 38265088 38281472 11 938 6185 25 _ _ (1746003 / 100000) (873003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38281472 :
    ThetaLowerSegment 38281472 38297856 (3827202197521 / 100000) (3828909830509 / 100000) := by
  exact
    packedTile8192 38281472 38297856 11 978 6187 25 _ _ (873023 / 50000) (1746049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38297856 :
    ThetaLowerSegment 38297856 38314240 (3828909830509 / 100000) (957639098109 / 25000) := by
  exact
    packedTile8192 38297856 38314240 11 943 6188 25 _ _ (1746089 / 100000) (436523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38314240 :
    ThetaLowerSegment 38314240 38330624 (957639098109 / 25000) (191610062439 / 5000) := by
  exact
    packedTile8192 38314240 38330624 11 942 6189 25 _ _ (436533 / 25000) (349227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38330624 :
    ThetaLowerSegment 38330624 38347008 (191610062439 / 5000) (19169125953 / 500) := by
  exact
    packedTile8192 38330624 38347008 11 930 6191 25 _ _ (873087 / 50000) (1746177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38347008 :
    ThetaLowerSegment 38347008 38363392 (19169125953 / 500) (3835402024551 / 100000) := by
  exact
    packedTile8192 38347008 38363392 11 903 6192 25 _ _ (1746217 / 100000) (87311 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38363392 :
    ThetaLowerSegment 38363392 38379776 (3835402024551 / 100000) (3837083672931 / 100000) := by
  exact
    packedTile8192 38363392 38379776 11 963 6193 25 _ _ (87313 / 5000) (1746263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38379776 :
    ThetaLowerSegment 38379776 38396160 (3837083672931 / 100000) (19193477553 / 500) := by
  exact
    packedTile8192 38379776 38396160 11 923 6195 25 _ _ (1746303 / 100000) (873153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38396160 :
    ThetaLowerSegment 38396160 38412544 (19193477553 / 500) (153612435189 / 4000) := by
  exact
    packedTile8192 38396160 38412544 11 925 6196 25 _ _ (349269 / 20000) (436587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38412544 :
    ThetaLowerSegment 38412544 38428928 (153612435189 / 4000) (3841982173041 / 100000) := by
  exact
    packedTile8192 38412544 38428928 11 957 6197 25 _ _ (436597 / 25000) (1746391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38428928 :
    ThetaLowerSegment 38428928 38445312 (3841982173041 / 100000) (3843679703973 / 100000) := by
  exact
    packedTile8192 38428928 38445312 11 972 6199 25 _ _ (1746431 / 100000) (873217 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38445312 :
    ThetaLowerSegment 38445312 38461696 (3843679703973 / 100000) (769051703113 / 20000) := by
  exact
    packedTile8192 38445312 38461696 11 904 6200 25 _ _ (1746473 / 100000) (436619 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38461696 :
    ThetaLowerSegment 38461696 38478080 (769051703113 / 20000) (3846912466217 / 100000) := by
  exact
    packedTile8192 38461696 38478080 11 947 6201 25 _ _ (436629 / 25000) (1746519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38478080 :
    ThetaLowerSegment 38478080 38494464 (3846912466217 / 100000) (3848514059903 / 100000) := by
  exact
    packedTile8192 38478080 38494464 11 917 6203 25 _ _ (873279 / 50000) (1746561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38494464 :
    ThetaLowerSegment 38494464 38510848 (3848514059903 / 100000) (1925111991141 / 50000) := by
  exact
    packedTile8192 38494464 38510848 11 979 6204 25 _ _ (1746601 / 100000) (436651 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38510848 :
    ThetaLowerSegment 38510848 38527232 (1925111991141 / 50000) (1925927673889 / 50000) := by
  exact
    packedTile8192 38510848 38527232 11 934 6205 25 _ _ (436661 / 25000) (1746647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38527232 :
    ThetaLowerSegment 38527232 38543616 (1925927673889 / 50000) (1926713682589 / 50000) := by
  exact
    packedTile8192 38527232 38543616 11 900 6207 25 _ _ (873343 / 50000) (1746689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38543616 :
    ThetaLowerSegment 38543616 38560000 (1926713682589 / 50000) (1927534645219 / 50000) := by
  exact
    packedTile8192 38543616 38560000 11 940 6208 25 _ _ (1746729 / 100000) (436683 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38560000 :
    ThetaLowerSegment 38560000 38576384 (1927534645219 / 50000) (3856674572987 / 100000) := by
  exact
    packedTile8192 38560000 38576384 11 919 6209 25 _ _ (1746771 / 100000) (873387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38576384 :
    ThetaLowerSegment 38576384 38592768 (3856674572987 / 100000) (3858335793101 / 100000) := by
  exact
    packedTile8192 38576384 38592768 11 951 6210 25 _ _ (873407 / 50000) (1746817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38592768 :
    ThetaLowerSegment 38592768 38609152 (3858335793101 / 100000) (3859955128613 / 100000) := by
  exact
    packedTile8192 38592768 38609152 11 927 6212 25 _ _ (218357 / 12500) (1746859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38609152 :
    ThetaLowerSegment 38609152 38625536 (3859955128613 / 100000) (3861583237549 / 100000) := by
  exact
    packedTile8192 38609152 38625536 11 932 6213 25 _ _ (873449 / 50000) (1746901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38625536 :
    ThetaLowerSegment 38625536 38641920 (3861583237549 / 100000) (3863186929387 / 100000) := by
  exact
    packedTile8192 38625536 38641920 11 918 6214 25 _ _ (1746941 / 100000) (54592 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38641920 :
    ThetaLowerSegment 38641920 38658304 (3863186929387 / 100000) (772967915061 / 20000) := by
  exact
    packedTile8192 38641920 38658304 11 946 6216 25 _ _ (1746983 / 100000) (873493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38658304 :
    ThetaLowerSegment 38658304 38674688 (772967915061 / 20000) (773292861897 / 20000) := by
  exact
    packedTile8192 38658304 38674688 11 930 6217 25 _ _ (873513 / 50000) (1747029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38674688 :
    ThetaLowerSegment 38674688 38691072 (773292861897 / 20000) (773624804817 / 20000) := by
  exact
    packedTile8192 38674688 38691072 11 950 6218 25 _ _ (436767 / 25000) (1747071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38691072 :
    ThetaLowerSegment 38691072 38707456 (773624804817 / 20000) (773957803983 / 20000) := by
  exact
    packedTile8192 38691072 38707456 11 953 6220 25 _ _ (174711 / 10000) (1747113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38707456 :
    ThetaLowerSegment 38707456 38723840 (773957803983 / 20000) (3871476769713 / 100000) := by
  exact
    packedTile8192 38707456 38723840 11 966 6221 25 _ _ (1747153 / 100000) (436789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38723840 :
    ThetaLowerSegment 38723840 38740224 (3871476769713 / 100000) (1936569176079 / 50000) := by
  exact
    packedTile8192 38723840 38740224 11 951 6222 25 _ _ (349439 / 20000) (873599 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38740224 :
    ThetaLowerSegment 38740224 38756608 (1936569176079 / 50000) (1937390377469 / 50000) := by
  exact
    packedTile8192 38740224 38756608 11 940 6224 25 _ _ (1747237 / 100000) (43681 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38756608 :
    ThetaLowerSegment 38756608 38772992 (1937390377469 / 50000) (1938203736309 / 50000) := by
  exact
    packedTile8192 38756608 38772992 11 931 6225 25 _ _ (21841 / 1250) (1747283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38772992 :
    ThetaLowerSegment 38772992 38789376 (1938203736309 / 50000) (484756025997 / 12500) := by
  exact
    packedTile8192 38772992 38789376 11 939 6226 25 _ _ (873661 / 50000) (69893 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38789376 :
    ThetaLowerSegment 38789376 38805760 (484756025997 / 12500) (484968330723 / 12500) := by
  exact
    packedTile8192 38789376 38805760 11 972 6228 25 _ _ (436841 / 25000) (1747367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38805760 :
    ThetaLowerSegment 38805760 38822144 (484968330723 / 12500) (77626770653 / 2000) := by
  exact
    packedTile8192 38805760 38822144 11 911 6229 25 _ _ (873703 / 50000) (1747409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38822144 :
    ThetaLowerSegment 38822144 38838528 (77626770653 / 2000) (121342832813 / 3125) := by
  exact
    packedTile8192 38822144 38838528 11 934 6230 25 _ _ (1747449 / 100000) (436863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38838528 :
    ThetaLowerSegment 38838528 38854912 (121342832813 / 3125) (971167302817 / 25000) := by
  exact
    packedTile8192 38838528 38854912 11 972 6232 25 _ _ (1747491 / 100000) (873747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38854912 :
    ThetaLowerSegment 38854912 38871296 (971167302817 / 25000) (971583215671 / 25000) := by
  exact
    packedTile8192 38854912 38871296 11 952 6233 25 _ _ (1747533 / 100000) (109221 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38871296 :
    ThetaLowerSegment 38871296 38887680 (971583215671 / 25000) (3887991311359 / 100000) := by
  exact
    packedTile8192 38871296 38887680 11 949 6234 25 _ _ (69903 / 4000) (873789 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38887680 :
    ThetaLowerSegment 38887680 38904064 (3887991311359 / 100000) (3889620090403 / 100000) := by
  exact
    packedTile8192 38887680 38904064 11 932 6235 25 _ _ (1747617 / 100000) (87381 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38904064 :
    ThetaLowerSegment 38904064 38920448 (3889620090403 / 100000) (3891266385181 / 100000) := by
  exact
    packedTile8192 38904064 38920448 11 942 6237 25 _ _ (1747659 / 100000) (873831 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38920448 :
    ThetaLowerSegment 38920448 38936832 (3891266385181 / 100000) (3892954665313 / 100000) := by
  exact
    packedTile8192 38920448 38936832 11 966 6238 25 _ _ (873851 / 50000) (349541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38936832 :
    ThetaLowerSegment 38936832 38953216 (3892954665313 / 100000) (3894590553697 / 100000) := by
  exact
    packedTile8192 38936832 38953216 11 936 6239 25 _ _ (54617 / 3125) (1747747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38953216 :
    ThetaLowerSegment 38953216 38969600 (3894590553697 / 100000) (3896191525673 / 100000) := by
  exact
    packedTile8192 38953216 38969600 11 916 6241 25 _ _ (873893 / 50000) (1747789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38969600 :
    ThetaLowerSegment 38969600 38985984 (3896191525673 / 100000) (3897790788293 / 100000) := by
  exact
    packedTile8192 38969600 38985984 11 915 6242 25 _ _ (436957 / 25000) (1747831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell38985984 :
    ThetaLowerSegment 38985984 39002368 (3897790788293 / 100000) (3899400576563 / 100000) := by
  exact
    packedTile8192 38985984 39002368 11 921 6243 25 _ _ (174787 / 10000) (1747873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39002368 :
    ThetaLowerSegment 39002368 39018752 (3899400576563 / 100000) (3901052353403 / 100000) := by
  exact
    packedTile8192 39002368 39018752 11 945 6245 25 _ _ (218489 / 12500) (349583 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39018752 :
    ThetaLowerSegment 39018752 39035136 (3901052353403 / 100000) (3902649983359 / 100000) := by
  exact
    packedTile8192 39018752 39035136 11 914 6246 25 _ _ (873977 / 50000) (1747957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39035136 :
    ThetaLowerSegment 39035136 39051520 (3902649983359 / 100000) (3904349035471 / 100000) := by
  exact
    packedTile8192 39035136 39051520 11 972 6247 25 _ _ (436999 / 25000) (1747999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39051520 :
    ThetaLowerSegment 39051520 39067904 (3904349035471 / 100000) (3905943246127 / 100000) := by
  exact
    packedTile8192 39051520 39067904 11 912 6249 25 _ _ (874019 / 50000) (1748041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39067904 :
    ThetaLowerSegment 39067904 39084288 (3905943246127 / 100000) (3907598677887 / 100000) := by
  exact
    packedTile8192 39067904 39084288 11 947 6250 25 _ _ (21851 / 1250) (1748083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39084288 :
    ThetaLowerSegment 39084288 39100672 (3907598677887 / 100000) (3909226179469 / 100000) := by
  exact
    packedTile8192 39084288 39100672 11 931 6251 25 _ _ (874061 / 50000) (2797 / 160) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39100672 :
    ThetaLowerSegment 39100672 39117056 (3909226179469 / 100000) (3910874698121 / 100000) := by
  exact
    packedTile8192 39100672 39117056 11 943 6253 25 _ _ (437041 / 25000) (1748167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39117056 :
    ThetaLowerSegment 39117056 39133440 (3910874698121 / 100000) (3912514514411 / 100000) := by
  exact
    packedTile8192 39117056 39133440 11 938 6254 25 _ _ (349641 / 20000) (109263 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39133440 :
    ThetaLowerSegment 39133440 39149824 (3912514514411 / 100000) (391418758679 / 10000) := by
  exact
    packedTile8192 39133440 39149824 11 957 6255 25 _ _ (1748247 / 100000) (6993 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39149824 :
    ThetaLowerSegment 39149824 39166208 (391418758679 / 10000) (3915846713051 / 100000) := by
  exact
    packedTile8192 39149824 39166208 11 949 6256 25 _ _ (1748289 / 100000) (437073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39166208 :
    ThetaLowerSegment 39166208 39182592 (3915846713051 / 100000) (979361608979 / 25000) := by
  exact
    packedTile8192 39166208 39182592 11 915 6258 25 _ _ (1748331 / 100000) (874167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39182592 :
    ThetaLowerSegment 39182592 39198976 (979361608979 / 25000) (489882741571 / 12500) := by
  exact
    packedTile8192 39182592 39198976 11 924 6259 25 _ _ (1748373 / 100000) (218547 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39198976 :
    ThetaLowerSegment 39198976 39215360 (489882741571 / 12500) (3920703694253 / 100000) := by
  exact
    packedTile8192 39198976 39215360 11 939 6260 25 _ _ (349683 / 20000) (874209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39215360 :
    ThetaLowerSegment 39215360 39231744 (3920703694253 / 100000) (3922401445029 / 100000) := by
  exact
    packedTile8192 39215360 39231744 11 971 6262 25 _ _ (218557 / 12500) (1748459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39231744 :
    ThetaLowerSegment 39231744 39248128 (3922401445029 / 100000) (784811454527 / 20000) := by
  exact
    packedTile8192 39231744 39248128 11 947 6263 25 _ _ (874249 / 50000) (1748501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39248128 :
    ThetaLowerSegment 39248128 39264512 (784811454527 / 20000) (785127590559 / 20000) := by
  exact
    packedTile8192 39248128 39264512 11 904 6264 25 _ _ (87427 / 5000) (1748543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39264512 :
    ThetaLowerSegment 39264512 39280896 (785127590559 / 20000) (3927313094351 / 100000) := by
  exact
    packedTile8192 39264512 39280896 11 958 6266 25 _ _ (874291 / 50000) (349717 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39280896 :
    ThetaLowerSegment 39280896 39297280 (3927313094351 / 100000) (1964517744003 / 50000) := by
  exact
    packedTile8192 39280896 39297280 11 985 6267 25 _ _ (1748623 / 100000) (874313 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39297280 :
    ThetaLowerSegment 39297280 39313664 (1964517744003 / 50000) (3930708960411 / 100000) := by
  exact
    packedTile8192 39297280 39313664 11 957 6268 25 _ _ (349733 / 20000) (437167 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39313664 :
    ThetaLowerSegment 39313664 39330048 (3930708960411 / 100000) (1966184241677 / 50000) := by
  exact
    packedTile8192 39313664 39330048 11 949 6270 25 _ _ (1748707 / 100000) (174871 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39330048 :
    ThetaLowerSegment 39330048 39346432 (1966184241677 / 50000) (1967001781367 / 50000) := by
  exact
    packedTile8192 39330048 39346432 11 935 6271 25 _ _ (437187 / 25000) (1748751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39346432 :
    ThetaLowerSegment 39346432 39362816 (1967001781367 / 50000) (122988927392 / 3125) := by
  exact
    packedTile8192 39346432 39362816 11 939 6272 25 _ _ (174879 / 10000) (1748793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39362816 :
    ThetaLowerSegment 39362816 39379200 (122988927392 / 3125) (24607874053 / 625) := by
  exact
    packedTile8192 39362816 39379200 11 923 6273 25 _ _ (54651 / 3125) (349767 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39379200 :
    ThetaLowerSegment 39379200 39395584 (24607874053 / 625) (3938881053751 / 100000) := by
  exact
    packedTile8192 39379200 39395584 11 927 6275 25 _ _ (1748873 / 100000) (437219 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39395584 :
    ThetaLowerSegment 39395584 39411968 (3938881053751 / 100000) (1970284378363 / 50000) := by
  exact
    packedTile8192 39395584 39411968 11 965 6276 25 _ _ (349783 / 20000) (874459 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39411968 :
    ThetaLowerSegment 39411968 39428352 (1970284378363 / 50000) (1971106388153 / 50000) := by
  exact
    packedTile8192 39411968 39428352 11 940 6277 25 _ _ (1748957 / 100000) (10931 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39428352 :
    ThetaLowerSegment 39428352 39444736 (1971106388153 / 50000) (1971919672223 / 50000) := by
  exact
    packedTile8192 39428352 39444736 11 930 6279 25 _ _ (874499 / 50000) (1749001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39444736 :
    ThetaLowerSegment 39444736 39461120 (1971919672223 / 50000) (1972732101303 / 50000) := by
  exact
    packedTile8192 39444736 39461120 11 929 6280 25 _ _ (21863 / 1250) (1749043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39461120 :
    ThetaLowerSegment 39461120 39477504 (1972732101303 / 50000) (3947075106207 / 100000) := by
  exact
    packedTile8192 39461120 39477504 11 921 6281 25 _ _ (1749081 / 100000) (437271 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39477504 :
    ThetaLowerSegment 39477504 39493888 (3947075106207 / 100000) (1974371010213 / 50000) := by
  exact
    packedTile8192 39477504 39493888 11 953 6283 25 _ _ (1749123 / 100000) (874563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39493888 :
    ThetaLowerSegment 39493888 39510272 (1974371010213 / 50000) (1975204486859 / 50000) := by
  exact
    packedTile8192 39493888 39510272 11 953 6284 25 _ _ (437291 / 25000) (1749167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39510272 :
    ThetaLowerSegment 39510272 39526656 (1975204486859 / 50000) (197604148193 / 5000) := by
  exact
    packedTile8192 39510272 39526656 11 957 6285 25 _ _ (874603 / 50000) (1749209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39526656 :
    ThetaLowerSegment 39526656 39543040 (197604148193 / 5000) (790743701961 / 20000) := by
  exact
    packedTile8192 39526656 39543040 11 935 6287 25 _ _ (1749247 / 100000) (6997 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39543040 :
    ThetaLowerSegment 39543040 39559424 (790743701961 / 20000) (791072568293 / 20000) := by
  exact
    packedTile8192 39543040 39559424 11 940 6288 25 _ _ (1749289 / 100000) (437323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39559424 :
    ThetaLowerSegment 39559424 39575808 (791072568293 / 20000) (158277979351 / 4000) := by
  exact
    packedTile8192 39559424 39575808 11 907 6289 25 _ _ (174933 / 10000) (1749333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39575808 :
    ThetaLowerSegment 39575808 39592192 (158277979351 / 4000) (395860263937 / 10000) := by
  exact
    packedTile8192 39575808 39592192 11 945 6290 25 _ _ (1749371 / 100000) (874687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39592192 :
    ThetaLowerSegment 39592192 39608576 (395860263937 / 10000) (3960276827611 / 100000) := by
  exact
    packedTile8192 39592192 39608576 11 957 6292 25 _ _ (1749413 / 100000) (218677 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39608576 :
    ThetaLowerSegment 39608576 39624960 (3960276827611 / 100000) (792396858943 / 20000) := by
  exact
    packedTile8192 39608576 39624960 11 976 6293 25 _ _ (874727 / 50000) (1749457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39624960 :
    ThetaLowerSegment 39624960 39641344 (792396858943 / 20000) (7927268137 / 200) := by
  exact
    packedTile8192 39624960 39641344 11 943 6294 25 _ _ (349899 / 20000) (874749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39641344 :
    ThetaLowerSegment 39641344 39657728 (7927268137 / 200) (3965255889299 / 100000) := by
  exact
    packedTile8192 39641344 39657728 11 927 6296 25 _ _ (1749537 / 100000) (87477 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39657728 :
    ThetaLowerSegment 39657728 39674112 (3965255889299 / 100000) (3966916238821 / 100000) := by
  exact
    packedTile8192 39657728 39674112 11 949 6297 25 _ _ (874789 / 50000) (1749581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39674112 :
    ThetaLowerSegment 39674112 39690496 (3966916238821 / 100000) (1984276066293 / 50000) := by
  exact
    packedTile8192 39674112 39690496 11 935 6298 25 _ _ (1749619 / 100000) (874811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39690496 :
    ThetaLowerSegment 39690496 39706880 (1984276066293 / 50000) (3970202062909 / 100000) := by
  exact
    packedTile8192 39690496 39706880 11 943 6300 25 _ _ (1749661 / 100000) (54677 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39706880 :
    ThetaLowerSegment 39706880 39723264 (3970202062909 / 100000) (794354659061 / 20000) := by
  exact
    packedTile8192 39706880 39723264 11 898 6301 25 _ _ (874851 / 50000) (349941 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39723264 :
    ThetaLowerSegment 39723264 39739648 (794354659061 / 20000) (124168275269 / 3125) := by
  exact
    packedTile8192 39723264 39739648 11 921 6302 25 _ _ (1749743 / 100000) (874873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39739648 :
    ThetaLowerSegment 39739648 39756032 (124168275269 / 3125) (248440443963 / 6250) := by
  exact
    packedTile8192 39739648 39756032 11 950 6303 25 _ _ (218723 / 12500) (1749787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39756032 :
    ThetaLowerSegment 39756032 39772416 (248440443963 / 6250) (994172110049 / 25000) := by
  exact
    packedTile8192 39756032 39772416 11 938 6305 25 _ _ (874913 / 50000) (1749829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39772416 :
    ThetaLowerSegment 39772416 39788800 (994172110049 / 25000) (198917715679 / 5000) := by
  exact
    packedTile8192 39772416 39788800 11 952 6306 25 _ _ (1749867 / 100000) (174987 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39788800 :
    ThetaLowerSegment 39788800 39805184 (198917715679 / 5000) (99499761939 / 2500) := by
  exact
    packedTile8192 39788800 39805184 11 935 6307 25 _ _ (437477 / 25000) (1749911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39805184 :
    ThetaLowerSegment 39805184 39821568 (99499761939 / 2500) (124424138483 / 3125) := by
  exact
    packedTile8192 39805184 39821568 11 904 6309 25 _ _ (1749949 / 100000) (54686 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39821568 :
    ThetaLowerSegment 39821568 39837952 (124424138483 / 3125) (1991600836073 / 50000) := by
  exact
    packedTile8192 39821568 39837952 11 931 6310 25 _ _ (174999 / 10000) (1749993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39837952 :
    ThetaLowerSegment 39837952 39854336 (1991600836073 / 50000) (1992432976289 / 50000) := by
  exact
    packedTile8192 39837952 39854336 11 951 6311 25 _ _ (109377 / 6250) (350007 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39854336 :
    ThetaLowerSegment 39854336 39870720 (1992432976289 / 50000) (1993248510307 / 50000) := by
  exact
    packedTile8192 39854336 39870720 11 932 6313 25 _ _ (1750073 / 100000) (437519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39870720 :
    ThetaLowerSegment 39870720 39887104 (1993248510307 / 50000) (79762282519 / 2000) := by
  exact
    packedTile8192 39870720 39887104 11 924 6314 25 _ _ (875057 / 50000) (1750117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39887104 :
    ThetaLowerSegment 39887104 39903488 (79762282519 / 2000) (797952204361 / 20000) := by
  exact
    packedTile8192 39887104 39903488 11 941 6315 25 _ _ (350031 / 20000) (875079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39903488 :
    ThetaLowerSegment 39903488 39919872 (797952204361 / 20000) (3991399205261 / 100000) := by
  exact
    packedTile8192 39903488 39919872 11 936 6316 25 _ _ (437549 / 25000) (1750199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39919872 :
    ThetaLowerSegment 39919872 39936256 (3991399205261 / 100000) (3993037427093 / 100000) := by
  exact
    packedTile8192 39919872 39936256 11 936 6318 25 _ _ (1750237 / 100000) (10939 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39936256 :
    ThetaLowerSegment 39936256 39952640 (3993037427093 / 100000) (3994591673957 / 100000) := by
  exact
    packedTile8192 39936256 39952640 11 888 6319 25 _ _ (875139 / 50000) (1750281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39952640 :
    ThetaLowerSegment 39952640 39969024 (3994591673957 / 100000) (1998117611749 / 50000) := by
  exact
    packedTile8192 39952640 39969024 11 939 6320 25 _ _ (1750319 / 100000) (875161 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39969024 :
    ThetaLowerSegment 39969024 39985408 (1998117611749 / 50000) (1998928028429 / 50000) := by
  exact
    packedTile8192 39969024 39985408 11 926 6322 25 _ _ (43759 / 2500) (1750363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell39985408 :
    ThetaLowerSegment 39985408 40001792 (1998928028429 / 50000) (1999757718503 / 50000) := by
  exact
    packedTile8192 39985408 40001792 11 948 6323 25 _ _ (1750401 / 100000) (437601 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40001792 :
    ThetaLowerSegment 40001792 40018176 (1999757718503 / 50000) (2000568173149 / 50000) := by
  exact
    packedTile8192 40001792 40018176 11 926 6324 25 _ _ (875221 / 50000) (350089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40018176 :
    ThetaLowerSegment 40018176 40034560 (2000568173149 / 50000) (2001387399193 / 50000) := by
  exact
    packedTile8192 40018176 40034560 11 936 6325 25 _ _ (1750483 / 100000) (875243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40034560 :
    ThetaLowerSegment 40034560 40050944 (2001387399193 / 50000) (2002186513399 / 50000) := by
  exact
    packedTile8192 40034560 40050944 11 913 6327 25 _ _ (437631 / 25000) (1750527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40050944 :
    ThetaLowerSegment 40050944 40067328 (2002186513399 / 50000) (4005995800553 / 100000) := by
  exact
    packedTile8192 40050944 40067328 11 927 6328 25 _ _ (350113 / 20000) (218821 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40067328 :
    ThetaLowerSegment 40067328 40083712 (4005995800553 / 100000) (4007646622011 / 100000) := by
  exact
    packedTile8192 40067328 40083712 11 943 6329 25 _ _ (875303 / 50000) (1750609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40083712 :
    ThetaLowerSegment 40083712 40100096 (4007646622011 / 100000) (2004671499477 / 50000) := by
  exact
    packedTile8192 40083712 40100096 11 969 6331 25 _ _ (1750647 / 100000) (35013 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40100096 :
    ThetaLowerSegment 40100096 40116480 (2004671499477 / 50000) (25068657146 / 625) := by
  exact
    packedTile8192 40100096 40116480 11 938 6332 25 _ _ (1750687 / 100000) (175069 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40116480 :
    ThetaLowerSegment 40116480 40132864 (25068657146 / 625) (501580385347 / 12500) := by
  exact
    packedTile8192 40116480 40132864 11 947 6333 25 _ _ (218841 / 12500) (1750731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40132864 :
    ThetaLowerSegment 40132864 40149248 (501580385347 / 12500) (2007142652049 / 50000) := by
  exact
    packedTile8192 40132864 40149248 11 938 6335 25 _ _ (1750769 / 100000) (437693 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40149248 :
    ThetaLowerSegment 40149248 40165632 (2007142652049 / 50000) (2007960280319 / 50000) := by
  exact
    packedTile8192 40149248 40165632 11 934 6336 25 _ _ (175081 / 10000) (1750813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40165632 :
    ThetaLowerSegment 40165632 40182016 (2007960280319 / 50000) (4017522589303 / 100000) := by
  exact
    packedTile8192 40165632 40182016 11 915 6337 25 _ _ (1750851 / 100000) (875427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40182016 :
    ThetaLowerSegment 40182016 40198400 (4017522589303 / 100000) (4019180684027 / 100000) := by
  exact
    packedTile8192 40182016 40198400 11 947 6338 25 _ _ (437723 / 25000) (350179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40198400 :
    ThetaLowerSegment 40198400 40214784 (4019180684027 / 100000) (32166248287 / 800) := by
  exact
    packedTile8192 40198400 40214784 11 914 6340 25 _ _ (437733 / 25000) (350187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40214784 :
    ThetaLowerSegment 40214784 40231168 (32166248287 / 800) (4022384927143 / 100000) := by
  exact
    packedTile8192 40214784 40231168 11 916 6341 25 _ _ (1750973 / 100000) (54718 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40231168 :
    ThetaLowerSegment 40231168 40247552 (4022384927143 / 100000) (4024023876247 / 100000) := by
  exact
    packedTile8192 40231168 40247552 11 936 6342 25 _ _ (875507 / 50000) (1751017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40247552 :
    ThetaLowerSegment 40247552 40263936 (4024023876247 / 100000) (4025650605413 / 100000) := by
  exact
    packedTile8192 40247552 40263936 11 929 6344 25 _ _ (875527 / 50000) (1751057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40263936 :
    ThetaLowerSegment 40263936 40280320 (4025650605413 / 100000) (125855701199 / 3125) := by
  exact
    packedTile8192 40263936 40280320 11 989 6345 25 _ _ (350219 / 20000) (875549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40280320 :
    ThetaLowerSegment 40280320 40296704 (125855701199 / 3125) (125907140819 / 3125) := by
  exact
    packedTile8192 40280320 40296704 11 940 6346 25 _ _ (54723 / 3125) (1751139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40296704 :
    ThetaLowerSegment 40296704 40313088 (125907140819 / 3125) (4030704382597 / 100000) := by
  exact
    packedTile8192 40296704 40313088 11 957 6347 25 _ _ (1751177 / 100000) (87559 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40313088 :
    ThetaLowerSegment 40313088 40329472 (4030704382597 / 100000) (4032378546049 / 100000) := by
  exact
    packedTile8192 40313088 40329472 11 956 6349 25 _ _ (1751217 / 100000) (87561 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40329472 :
    ThetaLowerSegment 40329472 40345856 (4032378546049 / 100000) (4033980947119 / 100000) := by
  exact
    packedTile8192 40329472 40345856 11 915 6350 25 _ _ (875629 / 50000) (1751261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40345856 :
    ThetaLowerSegment 40345856 40362240 (4033980947119 / 100000) (161427328351 / 4000) := by
  exact
    packedTile8192 40345856 40362240 11 972 6351 25 _ _ (875649 / 50000) (1751301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40362240 :
    ThetaLowerSegment 40362240 40378624 (161427328351 / 4000) (2018662106709 / 50000) := by
  exact
    packedTile8192 40362240 40378624 11 937 6353 25 _ _ (1751339 / 100000) (875671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40378624 :
    ThetaLowerSegment 40378624 40395008 (2018662106709 / 50000) (2019492260829 / 50000) := by
  exact
    packedTile8192 40378624 40395008 11 948 6354 25 _ _ (87569 / 5000) (1751383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40395008 :
    ThetaLowerSegment 40395008 40411392 (2019492260829 / 50000) (2020282151249 / 50000) := by
  exact
    packedTile8192 40395008 40411392 11 902 6355 25 _ _ (87571 / 5000) (1751423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40411392 :
    ThetaLowerSegment 40411392 40427776 (2020282151249 / 50000) (4042177398079 / 100000) := by
  exact
    packedTile8192 40411392 40427776 11 921 6356 25 _ _ (1751461 / 100000) (218933 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40427776 :
    ThetaLowerSegment 40427776 40444160 (4042177398079 / 100000) (4043795785003 / 100000) := by
  exact
    packedTile8192 40427776 40444160 11 924 6358 25 _ _ (1751501 / 100000) (109469 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40444160 :
    ThetaLowerSegment 40444160 40460544 (4043795785003 / 100000) (4045442234483 / 100000) := by
  exact
    packedTile8192 40444160 40460544 11 940 6359 25 _ _ (875771 / 50000) (350309 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40460544 :
    ThetaLowerSegment 40460544 40476928 (4045442234483 / 100000) (4047097479473 / 100000) := by
  exact
    packedTile8192 40460544 40476928 11 945 6360 25 _ _ (875791 / 50000) (350317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40476928 :
    ThetaLowerSegment 40476928 40493312 (4047097479473 / 100000) (2024367623489 / 50000) := by
  exact
    packedTile8192 40476928 40493312 11 935 6362 25 _ _ (1751623 / 100000) (875813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40493312 :
    ThetaLowerSegment 40493312 40509696 (2024367623489 / 50000) (4050376555209 / 100000) := by
  exact
    packedTile8192 40493312 40509696 11 937 6363 25 _ _ (1751663 / 100000) (875833 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40509696 :
    ThetaLowerSegment 40509696 40526080 (4050376555209 / 100000) (4052024908673 / 100000) := by
  exact
    packedTile8192 40509696 40526080 11 941 6364 25 _ _ (218963 / 12500) (1751707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40526080 :
    ThetaLowerSegment 40526080 40542464 (4052024908673 / 100000) (810733608909 / 20000) := by
  exact
    packedTile8192 40526080 40542464 11 938 6366 25 _ _ (54742 / 3125) (1751747 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40542464 :
    ThetaLowerSegment 40542464 40558848 (810733608909 / 20000) (5069062383 / 125) := by
  exact
    packedTile8192 40542464 40558848 11 903 6367 25 _ _ (350357 / 20000) (437947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40558848 :
    ThetaLowerSegment 40558848 40575232 (5069062383 / 125) (81137301781 / 2000) := by
  exact
    packedTile8192 40558848 40575232 11 922 6368 25 _ _ (70073 / 4000) (437957 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40575232 :
    ThetaLowerSegment 40575232 40591616 (81137301781 / 2000) (162338721821 / 4000) := by
  exact
    packedTile8192 40575232 40591616 11 915 6369 25 _ _ (350373 / 20000) (437967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40591616 :
    ThetaLowerSegment 40591616 40608000 (162338721821 / 4000) (4060107829541 / 100000) := by
  exact
    packedTile8192 40591616 40608000 11 936 6371 25 _ _ (875953 / 50000) (1751909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40608000 :
    ThetaLowerSegment 40608000 40624384 (4060107829541 / 100000) (4061730131537 / 100000) := by
  exact
    packedTile8192 40608000 40624384 11 926 6372 25 _ _ (875973 / 50000) (1751949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40624384 :
    ThetaLowerSegment 40624384 40640768 (4061730131537 / 100000) (4063343710643 / 100000) := by
  exact
    packedTile8192 40624384 40640768 11 921 6373 25 _ _ (875993 / 50000) (1751989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40640768 :
    ThetaLowerSegment 40640768 40657152 (4063343710643 / 100000) (508124484013 / 12500) := by
  exact
    packedTile8192 40640768 40657152 11 943 6375 25 _ _ (1752027 / 100000) (175203 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40657152 :
    ThetaLowerSegment 40657152 40673536 (508124484013 / 12500) (813326110123 / 20000) := by
  exact
    packedTile8192 40657152 40673536 11 933 6376 25 _ _ (1752067 / 100000) (175207 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40673536 :
    ThetaLowerSegment 40673536 40689920 (813326110123 / 20000) (1017056680023 / 25000) := by
  exact
    packedTile8192 40673536 40689920 11 911 6377 25 _ _ (1752107 / 100000) (175211 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40689920 :
    ThetaLowerSegment 40689920 40706304 (1017056680023 / 25000) (20349640279 / 500) := by
  exact
    packedTile8192 40689920 40706304 11 971 6378 25 _ _ (438037 / 25000) (1752151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40706304 :
    ThetaLowerSegment 40706304 40722688 (20349640279 / 500) (203580069767 / 5000) := by
  exact
    packedTile8192 40706304 40722688 11 955 6380 25 _ _ (438047 / 25000) (1752191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40722688 :
    ThetaLowerSegment 40722688 40739072 (203580069767 / 5000) (1018323511897 / 25000) := by
  exact
    packedTile8192 40722688 40739072 11 966 6381 25 _ _ (438057 / 25000) (1752231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40739072 :
    ThetaLowerSegment 40739072 40755456 (1018323511897 / 25000) (509368304539 / 12500) := by
  exact
    packedTile8192 40739072 40755456 11 943 6382 25 _ _ (438067 / 25000) (1752271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40755456 :
    ThetaLowerSegment 40755456 40771840 (509368304539 / 12500) (40765795883 / 1000) := by
  exact
    packedTile8192 40755456 40771840 11 932 6384 25 _ _ (1752309 / 100000) (219039 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40771840 :
    ThetaLowerSegment 40771840 40788224 (40765795883 / 1000) (4078260090991 / 100000) := by
  exact
    packedTile8192 40771840 40788224 11 959 6385 25 _ _ (1752349 / 100000) (54761 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40788224 :
    ThetaLowerSegment 40788224 40804608 (4078260090991 / 100000) (4079921355763 / 100000) := by
  exact
    packedTile8192 40788224 40804608 11 948 6386 25 _ _ (1752389 / 100000) (219049 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40804608 :
    ThetaLowerSegment 40804608 40820992 (4079921355763 / 100000) (51019016543 / 1250) := by
  exact
    packedTile8192 40804608 40820992 11 913 6387 25 _ _ (1752429 / 100000) (109527 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40820992 :
    ThetaLowerSegment 40820992 40837376 (51019016543 / 1250) (2041614114123 / 50000) := by
  exact
    packedTile8192 40820992 40837376 11 974 6389 25 _ _ (1752469 / 100000) (219059 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40837376 :
    ThetaLowerSegment 40837376 40853760 (2041614114123 / 50000) (408483352649 / 10000) := by
  exact
    packedTile8192 40837376 40853760 11 916 6390 25 _ _ (1752509 / 100000) (54766 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40853760 :
    ThetaLowerSegment 40853760 40870144 (408483352649 / 10000) (255407029277 / 6250) := by
  exact
    packedTile8192 40853760 40870144 11 958 6391 25 _ _ (1752549 / 100000) (219069 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40870144 :
    ThetaLowerSegment 40870144 40886528 (255407029277 / 6250) (1022032089103 / 25000) := by
  exact
    packedTile8192 40870144 40886528 11 922 6392 25 _ _ (175259 / 10000) (1752593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40886528 :
    ThetaLowerSegment 40886528 40902912 (1022032089103 / 25000) (2044841469611 / 50000) := by
  exact
    packedTile8192 40886528 40902912 11 887 6394 25 _ _ (175263 / 10000) (1752633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40902912 :
    ThetaLowerSegment 40902912 40919296 (2044841469611 / 50000) (127853145426 / 3125) := by
  exact
    packedTile8192 40902912 40919296 11 923 6395 25 _ _ (175267 / 10000) (1752673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40919296 :
    ThetaLowerSegment 40919296 40935680 (127853145426 / 3125) (2046459202481 / 50000) := by
  exact
    packedTile8192 40919296 40935680 11 923 6396 25 _ _ (175271 / 10000) (1752713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40935680 :
    ThetaLowerSegment 40935680 40952064 (2046459202481 / 50000) (2047267220231 / 50000) := by
  exact
    packedTile8192 40935680 40952064 11 922 6398 25 _ _ (7011 / 400) (1752753 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40952064 :
    ThetaLowerSegment 40952064 40968448 (2047267220231 / 50000) (512021662389 / 12500) := by
  exact
    packedTile8192 40952064 40968448 11 935 6399 25 _ _ (175279 / 10000) (1752793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40968448 :
    ThetaLowerSegment 40968448 40984832 (512021662389 / 12500) (2048918367391 / 50000) := by
  exact
    packedTile8192 40968448 40984832 11 949 6400 25 _ _ (175283 / 10000) (1752833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell40984832 :
    ThetaLowerSegment 40984832 41001216 (2048918367391 / 50000) (2049738710551 / 50000) := by
  exact
    packedTile8192 40984832 41001216 11 936 6401 25 _ _ (175287 / 10000) (1752873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41001216 :
    ThetaLowerSegment 41001216 41017600 (2049738710551 / 50000) (2050559072431 / 50000) := by
  exact
    packedTile8192 41001216 41017600 11 936 6403 25 _ _ (175291 / 10000) (1752913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41017600 :
    ThetaLowerSegment 41017600 41033984 (2050559072431 / 50000) (128210941916 / 3125) := by
  exact
    packedTile8192 41017600 41033984 11 931 6404 25 _ _ (35059 / 2000) (1752953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41033984 :
    ThetaLowerSegment 41033984 41050368 (128210941916 / 3125) (2052182322551 / 50000) := by
  exact
    packedTile8192 41033984 41050368 11 921 6405 25 _ _ (175299 / 10000) (1752993 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41050368 :
    ThetaLowerSegment 41050368 41066752 (2052182322551 / 50000) (513248712989 / 12500) := by
  exact
    packedTile8192 41050368 41066752 11 927 6407 25 _ _ (175303 / 10000) (1753033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41066752 :
    ThetaLowerSegment 41066752 41083136 (513248712989 / 12500) (410764109491 / 10000) := by
  exact
    packedTile8192 41066752 41083136 11 942 6408 25 _ _ (1753069 / 100000) (109567 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41083136 :
    ThetaLowerSegment 41083136 41099520 (410764109491 / 10000) (1027333649551 / 25000) := by
  exact
    packedTile8192 41083136 41099520 11 966 6409 25 _ _ (1753109 / 100000) (219139 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41099520 :
    ThetaLowerSegment 41099520 41115904 (1027333649551 / 25000) (2055479007089 / 50000) := by
  exact
    packedTile8192 41099520 41115904 11 926 6410 25 _ _ (1753149 / 100000) (54786 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41115904 :
    ThetaLowerSegment 41115904 41132288 (2055479007089 / 50000) (2056303005919 / 50000) := by
  exact
    packedTile8192 41115904 41132288 11 940 6412 25 _ _ (1753189 / 100000) (219149 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41132288 :
    ThetaLowerSegment 41132288 41148672 (2056303005919 / 50000) (164571073563 / 4000) := by
  exact
    packedTile8192 41132288 41148672 11 953 6413 25 _ _ (1753229 / 100000) (109577 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41148672 :
    ThetaLowerSegment 41148672 41165056 (164571073563 / 4000) (2057933527029 / 50000) := by
  exact
    packedTile8192 41148672 41165056 11 907 6414 25 _ _ (1753269 / 100000) (219159 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41165056 :
    ThetaLowerSegment 41165056 41181440 (2057933527029 / 50000) (4117523931063 / 100000) := by
  exact
    packedTile8192 41165056 41181440 11 945 6416 25 _ _ (1753309 / 100000) (54791 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41181440 :
    ThetaLowerSegment 41181440 41197824 (4117523931063 / 100000) (4119203638447 / 100000) := by
  exact
    packedTile8192 41181440 41197824 11 958 6417 25 _ _ (438337 / 25000) (1753351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41197824 :
    ThetaLowerSegment 41197824 41214208 (4119203638447 / 100000) (4120807988467 / 100000) := by
  exact
    packedTile8192 41197824 41214208 11 915 6418 25 _ _ (438347 / 25000) (1753391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41214208 :
    ThetaLowerSegment 41214208 41230592 (4120807988467 / 100000) (4122445690219 / 100000) := by
  exact
    packedTile8192 41214208 41230592 11 934 6419 25 _ _ (438357 / 25000) (1753431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41230592 :
    ThetaLowerSegment 41230592 41246976 (4122445690219 / 100000) (824815984479 / 20000) := by
  exact
    packedTile8192 41230592 41246976 11 932 6421 25 _ _ (438367 / 25000) (1753471 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41246976 :
    ThetaLowerSegment 41246976 41263360 (824815984479 / 20000) (4125668599737 / 100000) := by
  exact
    packedTile8192 41246976 41263360 11 906 6422 25 _ _ (1753507 / 100000) (175351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41263360 :
    ThetaLowerSegment 41263360 41279744 (4125668599737 / 100000) (4127292384259 / 100000) := by
  exact
    packedTile8192 41263360 41279744 11 926 6423 25 _ _ (1753547 / 100000) (35071 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41279744 :
    ThetaLowerSegment 41279744 41296128 (4127292384259 / 100000) (825790956947 / 20000) := by
  exact
    packedTile8192 41279744 41296128 11 948 6424 25 _ _ (1753587 / 100000) (175359 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41296128 :
    ThetaLowerSegment 41296128 41312512 (825790956947 / 20000) (4130566367029 / 100000) := by
  exact
    packedTile8192 41296128 41312512 11 919 6426 25 _ _ (876813 / 50000) (1753629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41312512 :
    ThetaLowerSegment 41312512 41328896 (4130566367029 / 100000) (826443313347 / 20000) := by
  exact
    packedTile8192 41312512 41328896 11 941 6427 25 _ _ (876833 / 50000) (1753669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41328896 :
    ThetaLowerSegment 41328896 41345280 (826443313347 / 20000) (826776517487 / 20000) := by
  exact
    packedTile8192 41328896 41345280 11 950 6428 25 _ _ (876853 / 50000) (1753709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41345280 :
    ThetaLowerSegment 41345280 41361664 (826776517487 / 20000) (413551532403 / 10000) := by
  exact
    packedTile8192 41345280 41361664 11 931 6430 25 _ _ (350749 / 20000) (438437 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41361664 :
    ThetaLowerSegment 41361664 41378048 (413551532403 / 10000) (827424007461 / 20000) := by
  exact
    packedTile8192 41361664 41378048 11 915 6431 25 _ _ (350757 / 20000) (438447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41378048 :
    ThetaLowerSegment 41378048 41394432 (827424007461 / 20000) (413874934073 / 10000) := by
  exact
    packedTile8192 41378048 41394432 11 929 6432 25 _ _ (70153 / 4000) (438457 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41394432 :
    ThetaLowerSegment 41394432 41410816 (413874934073 / 10000) (414037166493 / 10000) := by
  exact
    packedTile8192 41394432 41410816 11 925 6433 25 _ _ (219233 / 12500) (1753867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41410816 :
    ThetaLowerSegment 41410816 41427200 (414037166493 / 10000) (414197648709 / 10000) := by
  exact
    packedTile8192 41410816 41427200 11 915 6435 25 _ _ (109619 / 6250) (1753907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41427200 :
    ThetaLowerSegment 41427200 41443584 (414197648709 / 10000) (2071823120413 / 50000) := by
  exact
    packedTile8192 41427200 41443584 11 952 6436 25 _ _ (1753943 / 100000) (876973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41443584 :
    ThetaLowerSegment 41443584 41459968 (2071823120413 / 50000) (518166696559 / 12500) := by
  exact
    packedTile8192 41443584 41459968 11 962 6437 25 _ _ (1753983 / 100000) (876993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41459968 :
    ThetaLowerSegment 41459968 41476352 (518166696559 / 12500) (2073465743257 / 50000) := by
  exact
    packedTile8192 41459968 41476352 11 911 6438 25 _ _ (877011 / 50000) (70161 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41476352 :
    ThetaLowerSegment 41476352 41492736 (2073465743257 / 50000) (1037141129559 / 25000) := by
  exact
    packedTile8192 41476352 41492736 11 931 6440 25 _ _ (877031 / 50000) (350813 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41492736 :
    ThetaLowerSegment 41492736 41509120 (1037141129559 / 25000) (4150243192893 / 100000) := by
  exact
    packedTile8192 41492736 41509120 11 957 6441 25 _ _ (1754101 / 100000) (219263 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41509120 :
    ThetaLowerSegment 41509120 41525504 (4150243192893 / 100000) (259490075959 / 6250) := by
  exact
    packedTile8192 41509120 41525504 11 911 6442 25 _ _ (1754141 / 100000) (54817 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41525504 :
    ThetaLowerSegment 41525504 41541888 (259490075959 / 6250) (259591818399 / 6250) := by
  exact
    packedTile8192 41525504 41541888 11 928 6444 25 _ _ (87709 / 5000) (1754183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41541888 :
    ThetaLowerSegment 41541888 41558272 (259591818399 / 6250) (259697948709 / 6250) := by
  exact
    packedTile8192 41541888 41558272 11 968 6445 25 _ _ (87711 / 5000) (1754223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41558272 :
    ThetaLowerSegment 41558272 41574656 (259697948709 / 6250) (41567179443 / 1000) := by
  exact
    packedTile8192 41558272 41574656 11 884 6446 25 _ _ (1754259 / 100000) (877131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41574656 :
    ThetaLowerSegment 41574656 41591040 (41567179443 / 1000) (2079164195391 / 50000) := by
  exact
    packedTile8192 41574656 41591040 11 918 6447 25 _ _ (1754299 / 100000) (877151 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41591040 :
    ThetaLowerSegment 41591040 41607424 (2079164195391 / 50000) (1039985156851 / 25000) := by
  exact
    packedTile8192 41591040 41607424 11 919 6449 25 _ _ (877169 / 50000) (1754341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41607424 :
    ThetaLowerSegment 41607424 41623808 (1039985156851 / 25000) (2080779081499 / 50000) := by
  exact
    packedTile8192 41607424 41623808 11 922 6450 25 _ _ (1754377 / 100000) (87719 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41623808 :
    ThetaLowerSegment 41623808 41640192 (2080779081499 / 50000) (2081579095651 / 50000) := by
  exact
    packedTile8192 41623808 41640192 11 912 6451 25 _ _ (1754417 / 100000) (87721 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41640192 :
    ThetaLowerSegment 41640192 41656576 (2081579095651 / 50000) (2082399303831 / 50000) := by
  exact
    packedTile8192 41640192 41656576 11 935 6452 25 _ _ (219307 / 12500) (1754459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41656576 :
    ThetaLowerSegment 41656576 41672960 (2082399303831 / 50000) (4166456605437 / 100000) := by
  exact
    packedTile8192 41656576 41672960 11 945 6454 25 _ _ (350899 / 20000) (877249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41672960 :
    ThetaLowerSegment 41672960 41689344 (4166456605437 / 100000) (4168084813917 / 100000) := by
  exact
    packedTile8192 41672960 41689344 11 928 6455 25 _ _ (350907 / 20000) (877269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41689344 :
    ThetaLowerSegment 41689344 41705728 (4168084813917 / 100000) (4169767450383 / 100000) := by
  exact
    packedTile8192 41689344 41705728 11 959 6456 25 _ _ (877287 / 50000) (1754577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41705728 :
    ThetaLowerSegment 41705728 41722112 (4169767450383 / 100000) (1042845862239 / 25000) := by
  exact
    packedTile8192 41705728 41722112 11 921 6457 25 _ _ (1754613 / 100000) (219327 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41722112 :
    ThetaLowerSegment 41722112 41738496 (1042845862239 / 25000) (1043249432429 / 25000) := by
  exact
    packedTile8192 41722112 41738496 11 920 6459 25 _ _ (1754653 / 100000) (54833 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41738496 :
    ThetaLowerSegment 41738496 41754880 (1043249432429 / 25000) (1043664417087 / 25000) := by
  exact
    packedTile8192 41738496 41754880 11 946 6460 25 _ _ (438673 / 25000) (350939 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41754880 :
    ThetaLowerSegment 41754880 41771264 (1043664417087 / 25000) (2088158821937 / 50000) := by
  exact
    packedTile8192 41754880 41771264 11 946 6461 25 _ _ (1754731 / 100000) (877367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41771264 :
    ThetaLowerSegment 41771264 41787648 (2088158821937 / 50000) (1044485201531 / 25000) := by
  exact
    packedTile8192 41771264 41787648 11 925 6463 25 _ _ (175477 / 10000) (1754773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41787648 :
    ThetaLowerSegment 41787648 41804032 (1044485201531 / 25000) (2089808324837 / 50000) := by
  exact
    packedTile8192 41787648 41804032 11 955 6464 25 _ _ (175481 / 10000) (1754813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41804032 :
    ThetaLowerSegment 41804032 41820416 (2089808324837 / 50000) (2090633103867 / 50000) := by
  exact
    packedTile8192 41804032 41820416 11 940 6465 25 _ _ (1754849 / 100000) (438713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41820416 :
    ThetaLowerSegment 41820416 41836800 (2090633103867 / 50000) (418296318443 / 10000) := by
  exact
    packedTile8192 41820416 41836800 11 967 6466 25 _ _ (219361 / 12500) (1754891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41836800 :
    ThetaLowerSegment 41836800 41853184 (418296318443 / 10000) (4184597021467 / 100000) := by
  exact
    packedTile8192 41836800 41853184 11 931 6468 25 _ _ (1754927 / 100000) (175493 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41853184 :
    ThetaLowerSegment 41853184 41869568 (4184597021467 / 100000) (4186215100119 / 100000) := by
  exact
    packedTile8192 41853184 41869568 11 922 6469 25 _ _ (877483 / 50000) (1754969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41869568 :
    ThetaLowerSegment 41869568 41885952 (4186215100119 / 100000) (523481564973 / 12500) := by
  exact
    packedTile8192 41869568 41885952 11 933 6470 25 _ _ (351001 / 20000) (54844 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41885952 :
    ThetaLowerSegment 41885952 41902336 (523481564973 / 12500) (1047368545341 / 25000) := by
  exact
    packedTile8192 41885952 41902336 11 924 6471 25 _ _ (351009 / 20000) (219381 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41902336 :
    ThetaLowerSegment 41902336 41918720 (1047368545341 / 25000) (130971581679 / 3125) := by
  exact
    packedTile8192 41902336 41918720 11 921 6473 25 _ _ (438771 / 25000) (1755087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41918720 :
    ThetaLowerSegment 41918720 41935104 (130971581679 / 3125) (209635617369 / 5000) := by
  exact
    packedTile8192 41918720 41935104 11 924 6474 25 _ _ (1755123 / 100000) (877563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41935104 :
    ThetaLowerSegment 41935104 41951488 (209635617369 / 5000) (419431832061 / 10000) := by
  exact
    packedTile8192 41935104 41951488 11 915 6475 25 _ _ (877581 / 50000) (351033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41951488 :
    ThetaLowerSegment 41951488 41967872 (419431832061 / 10000) (4195955923143 / 100000) := by
  exact
    packedTile8192 41951488 41967872 11 933 6476 25 _ _ (1755201 / 100000) (438801 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41967872 :
    ThetaLowerSegment 41967872 41984256 (4195955923143 / 100000) (4197537394383 / 100000) := by
  exact
    packedTile8192 41967872 41984256 11 901 6478 25 _ _ (43881 / 2500) (1755243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell41984256 :
    ThetaLowerSegment 41984256 42000640 (4197537394383 / 100000) (524893811973 / 12500) := by
  exact
    packedTile8192 41984256 42000640 11 919 6479 25 _ _ (1755279 / 100000) (877641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42000640 :
    ThetaLowerSegment 42000640 42017024 (524893811973 / 12500) (2100401125011 / 50000) := by
  exact
    packedTile8192 42000640 42017024 11 941 6480 25 _ _ (877659 / 50000) (1755321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42017024 :
    ThetaLowerSegment 42017024 42033408 (2100401125011 / 50000) (52530083079 / 1250) := by
  exact
    packedTile8192 42017024 42033408 11 914 6482 25 _ _ (1755357 / 100000) (10971 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42033408 :
    ThetaLowerSegment 42033408 42049792 (52530083079 / 1250) (525508406367 / 12500) := by
  exact
    packedTile8192 42033408 42049792 11 946 6483 25 _ _ (438849 / 25000) (1755399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42049792 :
    ThetaLowerSegment 42049792 42066176 (525508406367 / 12500) (2102828837523 / 50000) := by
  exact
    packedTile8192 42049792 42066176 11 906 6484 25 _ _ (351087 / 20000) (877719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42066176 :
    ThetaLowerSegment 42066176 42082560 (2102828837523 / 50000) (525912819273 / 12500) := by
  exact
    packedTile8192 42066176 42082560 11 937 6485 25 _ _ (877737 / 50000) (1755477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42082560 :
    ThetaLowerSegment 42082560 42098944 (525912819273 / 12500) (2104488656793 / 50000) := by
  exact
    packedTile8192 42082560 42098944 11 954 6487 25 _ _ (1755513 / 100000) (438879 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42098944 :
    ThetaLowerSegment 42098944 42115328 (2104488656793 / 50000) (2105300599593 / 50000) := by
  exact
    packedTile8192 42098944 42115328 11 925 6488 25 _ _ (54861 / 3125) (351111 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42115328 :
    ThetaLowerSegment 42115328 42131712 (2105300599593 / 50000) (4212211076133 / 100000) := by
  exact
    packedTile8192 42115328 42131712 11 917 6489 25 _ _ (1755591 / 100000) (877797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42131712 :
    ThetaLowerSegment 42131712 42148096 (4212211076133 / 100000) (4213912281603 / 100000) := by
  exact
    packedTile8192 42131712 42148096 11 969 6490 25 _ _ (175563 / 10000) (1755633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42148096 :
    ThetaLowerSegment 42148096 42164480 (4213912281603 / 100000) (2107776916059 / 50000) := by
  exact
    packedTile8192 42148096 42164480 11 935 6492 25 _ _ (1755669 / 100000) (219459 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42164480 :
    ThetaLowerSegment 42164480 42180864 (2107776916059 / 50000) (4217216486647 / 100000) := by
  exact
    packedTile8192 42164480 42180864 11 947 6493 25 _ _ (1755707 / 100000) (175571 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42180864 :
    ThetaLowerSegment 42180864 42197248 (4217216486647 / 100000) (4218844063189 / 100000) := by
  exact
    packedTile8192 42180864 42197248 11 927 6494 25 _ _ (877873 / 50000) (1755749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42197248 :
    ThetaLowerSegment 42197248 42213632 (4218844063189 / 100000) (4220498012659 / 100000) := by
  exact
    packedTile8192 42197248 42213632 11 942 6495 25 _ _ (351157 / 20000) (438947 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42213632 :
    ThetaLowerSegment 42213632 42230016 (4220498012659 / 100000) (4222151998867 / 100000) := by
  exact
    packedTile8192 42213632 42230016 11 942 6497 25 _ _ (109739 / 6250) (1755827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42230016 :
    ThetaLowerSegment 42230016 42246400 (4222151998867 / 100000) (2111905644701 / 50000) := by
  exact
    packedTile8192 42230016 42246400 11 945 6498 25 _ _ (1755863 / 100000) (877933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42246400 :
    ThetaLowerSegment 42246400 42262784 (2111905644701 / 50000) (211272916227 / 5000) := by
  exact
    packedTile8192 42246400 42262784 11 938 6499 25 _ _ (1755901 / 100000) (54872 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42262784 :
    ThetaLowerSegment 42262784 42279168 (211272916227 / 5000) (211355621001 / 5000) := by
  exact
    packedTile8192 42262784 42279168 11 942 6500 25 _ _ (87797 / 5000) (1755943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42279168 :
    ThetaLowerSegment 42279168 42295552 (211355621001 / 5000) (169150872807 / 4000) := by
  exact
    packedTile8192 42279168 42295552 11 945 6502 25 _ _ (1755979 / 100000) (877991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42295552 :
    ThetaLowerSegment 42295552 42311936 (169150872807 / 4000) (4230505009941 / 100000) := by
  exact
    packedTile8192 42295552 42311936 11 987 6503 25 _ _ (878009 / 50000) (1756021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42311936 :
    ThetaLowerSegment 42311936 42328320 (4230505009941 / 100000) (4232076680061 / 100000) := by
  exact
    packedTile8192 42311936 42328320 11 895 6504 25 _ _ (219507 / 12500) (1756059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42328320 :
    ThetaLowerSegment 42328320 42344704 (4232076680061 / 100000) (1058430535269 / 25000) := by
  exact
    packedTile8192 42328320 42344704 11 937 6506 25 _ _ (351219 / 20000) (878049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42344704 :
    ThetaLowerSegment 42344704 42361088 (1058430535269 / 25000) (132354854553 / 3125) := by
  exact
    packedTile8192 42344704 42361088 11 930 6507 25 _ _ (878067 / 50000) (1756137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42361088 :
    ThetaLowerSegment 42361088 42377472 (132354854553 / 3125) (2118511855023 / 50000) := by
  exact
    packedTile8192 42361088 42377472 11 950 6508 25 _ _ (1756173 / 100000) (109761 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42377472 :
    ThetaLowerSegment 42377472 42393856 (2118511855023 / 50000) (2119316199661 / 50000) := by
  exact
    packedTile8192 42377472 42393856 11 916 6509 25 _ _ (1756211 / 100000) (878107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42393856 :
    ThetaLowerSegment 42393856 42410240 (2119316199661 / 50000) (1060065988893 / 25000) := by
  exact
    packedTile8192 42393856 42410240 11 929 6511 25 _ _ (281 / 16) (1756253 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42410240 :
    ThetaLowerSegment 42410240 42426624 (1060065988893 / 25000) (4241867447429 / 100000) := by
  exact
    packedTile8192 42410240 42426624 11 913 6512 25 _ _ (1756289 / 100000) (439073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42426624 :
    ThetaLowerSegment 42426624 42443008 (4241867447429 / 100000) (848699463777 / 20000) := by
  exact
    packedTile8192 42426624 42443008 11 928 6513 25 _ _ (1756327 / 100000) (175633 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42443008 :
    ThetaLowerSegment 42443008 42459392 (848699463777 / 20000) (4245160597487 / 100000) := by
  exact
    packedTile8192 42443008 42459392 11 947 6514 25 _ _ (878183 / 50000) (1756369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42459392 :
    ThetaLowerSegment 42459392 42475776 (4245160597487 / 100000) (849363026011 / 20000) := by
  exact
    packedTile8192 42459392 42475776 11 942 6516 25 _ _ (439101 / 25000) (1756407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42475776 :
    ThetaLowerSegment 42475776 42483968 (849363026011 / 20000) (4247661735581 / 100000) := by
  exact
    packedTile8192 42475776 42483968 10 482 6517 25 _ _ (1756443 / 100000) (878223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42483968 :
    ThetaLowerSegment 42483968 42488064 (4247661735581 / 100000) (4248067478303 / 100000) := by
  exact
    packedTile8192 42483968 42488064 9 231 6517 25 _ _ (878231 / 50000) (351293 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_31072512_42488064 :
    ThetaLowerSegment 31072512 42488064 (3106694022169 / 100000) (4248067478303 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31072512 cell31088896)
                      (ThetaLowerSegment.join cell31105280 cell31121664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31138048 cell31154432)
                      (ThetaLowerSegment.join cell31170816 cell31187200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31203584 cell31219968)
                      (ThetaLowerSegment.join cell31236352 cell31252736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31269120 cell31285504)
                      (ThetaLowerSegment.join cell31301888 cell31318272))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31334656 cell31351040)
                      (ThetaLowerSegment.join cell31367424 cell31383808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31400192 cell31416576)
                      (ThetaLowerSegment.join cell31432960 cell31449344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31465728 cell31482112)
                      (ThetaLowerSegment.join cell31498496 cell31514880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31531264 cell31547648)
                      (ThetaLowerSegment.join cell31564032 cell31580416)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31596800 cell31613184)
                      (ThetaLowerSegment.join cell31629568 cell31645952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31662336 cell31678720)
                      (ThetaLowerSegment.join cell31695104 cell31711488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31727872 cell31744256)
                      (ThetaLowerSegment.join cell31760640 cell31777024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31793408 cell31809792)
                      (ThetaLowerSegment.join cell31826176 cell31842560))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31858944 cell31875328)
                      (ThetaLowerSegment.join cell31891712 cell31908096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31924480 cell31940864)
                      (ThetaLowerSegment.join cell31957248 cell31973632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell31990016 cell32006400)
                      (ThetaLowerSegment.join cell32022784 cell32039168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32055552 cell32071936)
                      (ThetaLowerSegment.join cell32088320 cell32104704))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32121088 cell32137472)
                      (ThetaLowerSegment.join cell32153856 cell32170240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32186624 cell32203008)
                      (ThetaLowerSegment.join cell32219392 cell32235776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32252160 cell32268544)
                      (ThetaLowerSegment.join cell32284928 cell32301312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32317696 cell32334080)
                      (ThetaLowerSegment.join cell32350464 cell32366848))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32383232 cell32399616)
                      (ThetaLowerSegment.join cell32416000 cell32432384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32448768 cell32465152)
                      (ThetaLowerSegment.join cell32481536 cell32497920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32514304 cell32530688)
                      (ThetaLowerSegment.join cell32547072 cell32563456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32579840 cell32596224)
                      (ThetaLowerSegment.join cell32612608 cell32628992)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32645376 cell32661760)
                      (ThetaLowerSegment.join cell32678144 cell32694528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32710912 cell32727296)
                      (ThetaLowerSegment.join cell32743680 cell32760064)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32776448 cell32792832)
                      (ThetaLowerSegment.join cell32809216 cell32825600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32841984 cell32858368)
                      (ThetaLowerSegment.join cell32874752 cell32891136))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32907520 cell32923904)
                      (ThetaLowerSegment.join cell32940288 cell32956672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell32973056 cell32989440)
                      (ThetaLowerSegment.join cell33005824 cell33022208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33038592 cell33054976)
                      (ThetaLowerSegment.join cell33071360 cell33087744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33104128 cell33120512)
                      (ThetaLowerSegment.join cell33136896 cell33153280)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33169664 cell33186048)
                      (ThetaLowerSegment.join cell33202432 cell33218816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33235200 cell33251584)
                      (ThetaLowerSegment.join cell33267968 cell33284352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33300736 cell33317120)
                      (ThetaLowerSegment.join cell33333504 cell33349888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33366272 cell33382656)
                      (ThetaLowerSegment.join cell33399040 cell33415424))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33431808 cell33448192)
                      (ThetaLowerSegment.join cell33464576 cell33480960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33497344 cell33513728)
                      (ThetaLowerSegment.join cell33530112 cell33546496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33562880 cell33579264)
                      (ThetaLowerSegment.join cell33595648 cell33612032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33628416 cell33644800)
                      (ThetaLowerSegment.join cell33661184 cell33677568)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33693952 cell33710336)
                      (ThetaLowerSegment.join cell33726720 cell33743104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33759488 cell33775872)
                      (ThetaLowerSegment.join cell33792256 cell33808640)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33825024 cell33841408)
                      (ThetaLowerSegment.join cell33857792 cell33874176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33890560 cell33906944)
                      (ThetaLowerSegment.join cell33923328 cell33939712))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell33956096 cell33972480)
                      (ThetaLowerSegment.join cell33988864 cell34005248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34021632 cell34038016)
                      (ThetaLowerSegment.join cell34054400 cell34070784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34087168 cell34103552)
                      (ThetaLowerSegment.join cell34119936 cell34136320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34152704 cell34169088)
                      (ThetaLowerSegment.join cell34185472 cell34201856))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34218240 cell34234624)
                      (ThetaLowerSegment.join cell34251008 cell34267392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34283776 cell34300160)
                      (ThetaLowerSegment.join cell34316544 cell34332928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34349312 cell34365696)
                      (ThetaLowerSegment.join cell34382080 cell34398464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34414848 cell34431232)
                      (ThetaLowerSegment.join cell34447616 cell34464000))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34480384 cell34496768)
                      (ThetaLowerSegment.join cell34513152 cell34529536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34545920 cell34562304)
                      (ThetaLowerSegment.join cell34578688 cell34595072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34611456 cell34627840)
                      (ThetaLowerSegment.join cell34644224 cell34660608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34676992 cell34693376)
                      (ThetaLowerSegment.join cell34709760 cell34726144)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34742528 cell34758912)
                      (ThetaLowerSegment.join cell34775296 cell34791680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34808064 cell34824448)
                      (ThetaLowerSegment.join cell34840832 cell34857216)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34873600 cell34889984)
                      (ThetaLowerSegment.join cell34906368 cell34922752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell34939136 cell34955520)
                      (ThetaLowerSegment.join cell34971904 cell34988288))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35004672 cell35021056)
                      (ThetaLowerSegment.join cell35037440 cell35053824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35070208 cell35086592)
                      (ThetaLowerSegment.join cell35102976 cell35119360)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35135744 cell35152128)
                      (ThetaLowerSegment.join cell35168512 cell35184896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35201280 cell35217664)
                      (ThetaLowerSegment.join cell35234048 cell35250432))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35266816 cell35283200)
                      (ThetaLowerSegment.join cell35299584 cell35315968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35332352 cell35348736)
                      (ThetaLowerSegment.join cell35365120 cell35381504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35397888 cell35414272)
                      (ThetaLowerSegment.join cell35430656 cell35447040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35463424 cell35479808)
                      (ThetaLowerSegment.join cell35496192 cell35512576))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35528960 cell35545344)
                      (ThetaLowerSegment.join cell35561728 cell35578112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35594496 cell35610880)
                      (ThetaLowerSegment.join cell35627264 cell35643648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35660032 cell35676416)
                      (ThetaLowerSegment.join cell35692800 cell35709184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35725568 cell35741952)
                      (ThetaLowerSegment.join cell35758336 cell35774720)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35791104 cell35807488)
                      (ThetaLowerSegment.join cell35823872 cell35840256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35856640 cell35873024)
                      (ThetaLowerSegment.join cell35889408 cell35905792)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35922176 cell35938560)
                      (ThetaLowerSegment.join cell35954944 cell35971328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell35987712 cell36004096)
                      (ThetaLowerSegment.join cell36020480 cell36036864))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36053248 cell36069632)
                      (ThetaLowerSegment.join cell36086016 cell36102400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36118784 cell36135168)
                      (ThetaLowerSegment.join cell36151552 cell36167936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36184320 cell36200704)
                      (ThetaLowerSegment.join cell36217088 cell36233472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36249856 cell36266240)
                      (ThetaLowerSegment.join cell36282624 cell36299008))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36315392 cell36331776)
                      (ThetaLowerSegment.join cell36348160 cell36364544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36380928 cell36397312)
                      (ThetaLowerSegment.join cell36413696 cell36430080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36446464 cell36462848)
                      (ThetaLowerSegment.join cell36479232 cell36495616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36512000 cell36528384)
                      (ThetaLowerSegment.join cell36544768 cell36561152))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36577536 cell36593920)
                      (ThetaLowerSegment.join cell36610304 cell36626688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36643072 cell36659456)
                      (ThetaLowerSegment.join cell36675840 cell36692224)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36708608 cell36724992)
                      (ThetaLowerSegment.join cell36741376 cell36757760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36774144 cell36790528)
                      (ThetaLowerSegment.join cell36806912 cell36823296)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36839680 cell36856064)
                      (ThetaLowerSegment.join cell36872448 cell36888832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36905216 cell36921600)
                      (ThetaLowerSegment.join cell36937984 cell36954368)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell36970752 cell36987136)
                      (ThetaLowerSegment.join cell37003520 cell37019904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37036288 cell37052672)
                      (ThetaLowerSegment.join cell37069056 cell37085440))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37101824 cell37118208)
                      (ThetaLowerSegment.join cell37134592 cell37150976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37167360 cell37183744)
                      (ThetaLowerSegment.join cell37200128 cell37216512)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37232896 cell37249280)
                      (ThetaLowerSegment.join cell37265664 cell37282048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37298432 cell37314816)
                      (ThetaLowerSegment.join cell37331200 cell37347584)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37363968 cell37380352)
                      (ThetaLowerSegment.join cell37396736 cell37413120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37429504 cell37445888)
                      (ThetaLowerSegment.join cell37462272 cell37478656)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37495040 cell37511424)
                      (ThetaLowerSegment.join cell37527808 cell37544192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37560576 cell37576960)
                      (ThetaLowerSegment.join cell37593344 cell37609728))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37626112 cell37642496)
                      (ThetaLowerSegment.join cell37658880 cell37675264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37691648 cell37708032)
                      (ThetaLowerSegment.join cell37724416 cell37740800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37757184 cell37773568)
                      (ThetaLowerSegment.join cell37789952 cell37806336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37822720 cell37839104)
                      (ThetaLowerSegment.join cell37855488 cell37871872)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37888256 cell37904640)
                      (ThetaLowerSegment.join cell37921024 cell37937408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell37953792 cell37970176)
                      (ThetaLowerSegment.join cell37986560 cell38002944)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38019328 cell38035712)
                      (ThetaLowerSegment.join cell38052096 cell38068480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38084864 cell38101248)
                      (ThetaLowerSegment.join cell38117632 cell38134016))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38150400 cell38166784)
                      (ThetaLowerSegment.join cell38183168 cell38199552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38215936 cell38232320)
                      (ThetaLowerSegment.join cell38248704 cell38265088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38281472 cell38297856)
                      (ThetaLowerSegment.join cell38314240 cell38330624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38347008 cell38363392)
                      (ThetaLowerSegment.join cell38379776 cell38396160))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38412544 cell38428928)
                      (ThetaLowerSegment.join cell38445312 cell38461696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38478080 cell38494464)
                      (ThetaLowerSegment.join cell38510848 cell38527232)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38543616 cell38560000)
                      (ThetaLowerSegment.join cell38576384 cell38592768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38609152 cell38625536)
                      (ThetaLowerSegment.join cell38641920 cell38658304))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38674688 cell38691072)
                      (ThetaLowerSegment.join cell38707456 cell38723840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38740224 cell38756608)
                      (ThetaLowerSegment.join cell38772992 cell38789376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38805760 cell38822144)
                      (ThetaLowerSegment.join cell38838528 cell38854912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38871296 cell38887680)
                      (ThetaLowerSegment.join cell38904064 cell38920448)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell38936832 cell38953216)
                      (ThetaLowerSegment.join cell38969600 cell38985984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell39002368 cell39018752)
                      (ThetaLowerSegment.join cell39035136 cell39051520)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell39067904 cell39084288)
                      (ThetaLowerSegment.join cell39100672 cell39117056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell39133440 cell39149824)
                      (ThetaLowerSegment.join cell39166208 cell39182592))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell39198976 cell39215360)
                      (ThetaLowerSegment.join cell39231744 cell39248128))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell39264512 cell39280896)
                      (ThetaLowerSegment.join cell39297280 cell39313664)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell39330048 cell39346432)
                      (ThetaLowerSegment.join cell39362816 cell39379200))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell39395584 cell39411968)
                      (ThetaLowerSegment.join cell39428352 cell39444736)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39461120 cell39477504)
                    (ThetaLowerSegment.join cell39493888 cell39510272))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39526656 cell39543040)
                    (ThetaLowerSegment.join cell39559424 cell39575808)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39592192 cell39608576)
                    (ThetaLowerSegment.join cell39624960 cell39641344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39657728 cell39674112)
                    (ThetaLowerSegment.join cell39690496 cell39706880))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39723264 cell39739648)
                    (ThetaLowerSegment.join cell39756032 cell39772416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39788800 cell39805184)
                    (ThetaLowerSegment.join cell39821568 cell39837952)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39854336 cell39870720)
                    (ThetaLowerSegment.join cell39887104 cell39903488))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39919872 cell39936256)
                    (ThetaLowerSegment.join cell39952640 cell39969024)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell39985408 cell40001792)
                    (ThetaLowerSegment.join cell40018176 cell40034560))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40050944 cell40067328)
                    (ThetaLowerSegment.join cell40083712 cell40100096)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40116480 cell40132864)
                    (ThetaLowerSegment.join cell40149248 cell40165632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40182016 cell40198400)
                    (ThetaLowerSegment.join cell40214784 cell40231168))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40247552 cell40263936)
                    (ThetaLowerSegment.join cell40280320 cell40296704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40313088 cell40329472)
                    (ThetaLowerSegment.join cell40345856 cell40362240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40378624 cell40395008)
                    (ThetaLowerSegment.join cell40411392 cell40427776))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40444160 cell40460544)
                    (ThetaLowerSegment.join cell40476928 cell40493312))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40509696 cell40526080)
                    (ThetaLowerSegment.join cell40542464 cell40558848))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40575232 cell40591616)
                    (ThetaLowerSegment.join cell40608000 cell40624384)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40640768 cell40657152)
                    (ThetaLowerSegment.join cell40673536 cell40689920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40706304 cell40722688)
                    (ThetaLowerSegment.join cell40739072 cell40755456))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40771840 cell40788224)
                    (ThetaLowerSegment.join cell40804608 cell40820992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40837376 cell40853760)
                    (ThetaLowerSegment.join cell40870144 cell40886528)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40902912 cell40919296)
                    (ThetaLowerSegment.join cell40935680 cell40952064))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell40968448 cell40984832)
                    (ThetaLowerSegment.join cell41001216 cell41017600)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41033984 cell41050368)
                    (ThetaLowerSegment.join cell41066752 cell41083136))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41099520 cell41115904)
                    (ThetaLowerSegment.join cell41132288 cell41148672)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41165056 cell41181440)
                    (ThetaLowerSegment.join cell41197824 cell41214208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41230592 cell41246976)
                    (ThetaLowerSegment.join cell41263360 cell41279744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41296128 cell41312512)
                    (ThetaLowerSegment.join cell41328896 cell41345280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41361664 cell41378048)
                    (ThetaLowerSegment.join cell41394432 cell41410816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41427200 cell41443584)
                    (ThetaLowerSegment.join cell41459968 cell41476352))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell41492736 cell41509120)
                    (ThetaLowerSegment.join cell41525504 cell41541888)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell41558272 cell41574656)
                  (ThetaLowerSegment.join cell41591040 cell41607424))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell41623808 cell41640192)
                  (ThetaLowerSegment.join cell41656576 cell41672960)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell41689344 cell41705728)
                  (ThetaLowerSegment.join cell41722112 cell41738496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell41754880 cell41771264)
                  (ThetaLowerSegment.join cell41787648 cell41804032))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell41820416 cell41836800)
                  (ThetaLowerSegment.join cell41853184 cell41869568))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell41885952 cell41902336)
                  (ThetaLowerSegment.join cell41918720 cell41935104)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell41951488 cell41967872)
                  (ThetaLowerSegment.join cell41984256 cell42000640))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell42017024 cell42033408)
                  (ThetaLowerSegment.join cell42049792 cell42066176)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell42082560 cell42098944)
                  (ThetaLowerSegment.join cell42115328 cell42131712))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell42148096 cell42164480)
                  (ThetaLowerSegment.join cell42180864 cell42197248)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell42213632 cell42230016)
                  (ThetaLowerSegment.join cell42246400 cell42262784))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell42279168 cell42295552)
                  (ThetaLowerSegment.join cell42311936 cell42328320))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell42344704 cell42361088)
                  (ThetaLowerSegment.join cell42377472 cell42393856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell42410240 cell42426624)
                  (ThetaLowerSegment.join cell42443008 cell42459392)))
              (ThetaLowerSegment.join cell42475776 cell42483968))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
