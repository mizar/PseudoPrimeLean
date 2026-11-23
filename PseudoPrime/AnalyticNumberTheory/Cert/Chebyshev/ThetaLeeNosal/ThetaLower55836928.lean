/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis8192

/-! # Direct theta estimate up to 55836928 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell42488064 :
    ThetaLowerSegment 42488064 42504448 (4248067478303 / 100000) (4249722074927 / 100000) := by
  exact
    packedTile8192 42488064 42504448 11 942 6518 25 _ _ (219559 / 12500) (70259 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42504448 :
    ThetaLowerSegment 42504448 42520832 (4249722074927 / 100000) (4251359142247 / 100000) := by
  exact
    packedTile8192 42504448 42520832 11 932 6519 25 _ _ (175651 / 10000) (1756513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42520832 :
    ThetaLowerSegment 42520832 42537216 (4251359142247 / 100000) (2126479679193 / 50000) := by
  exact
    packedTile8192 42520832 42537216 11 911 6520 25 _ _ (1756549 / 100000) (219569 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42537216 :
    ThetaLowerSegment 42537216 42553600 (2126479679193 / 50000) (531827636211 / 12500) := by
  exact
    packedTile8192 42537216 42553600 11 946 6522 25 _ _ (1756587 / 100000) (175659 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42553600 :
    ThetaLowerSegment 42553600 42569984 (531827636211 / 12500) (2128117714491 / 50000) := by
  exact
    packedTile8192 42553600 42569984 11 919 6523 25 _ _ (878313 / 50000) (1756629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42569984 :
    ThetaLowerSegment 42569984 42586368 (2128117714491 / 50000) (2128915239947 / 50000) := by
  exact
    packedTile8192 42569984 42586368 11 908 6524 25 _ _ (219583 / 12500) (1756667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42586368 :
    ThetaLowerSegment 42586368 42602752 (2128915239947 / 50000) (4259462456981 / 100000) := by
  exact
    packedTile8192 42586368 42602752 11 929 6525 25 _ _ (1756703 / 100000) (878353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42602752 :
    ThetaLowerSegment 42602752 42619136 (4259462456981 / 100000) (4261117307003 / 100000) := by
  exact
    packedTile8192 42602752 42619136 11 942 6527 25 _ _ (1756741 / 100000) (219593 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42619136 :
    ThetaLowerSegment 42619136 42635520 (4261117307003 / 100000) (4262726517483 / 100000) := by
  exact
    packedTile8192 42619136 42635520 11 916 6528 25 _ _ (87839 / 5000) (1756783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42635520 :
    ThetaLowerSegment 42635520 42651904 (4262726517483 / 100000) (4264404278673 / 100000) := by
  exact
    packedTile8192 42635520 42651904 11 955 6529 25 _ _ (878409 / 50000) (1756821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42651904 :
    ThetaLowerSegment 42651904 42668288 (4264404278673 / 100000) (4266073292823 / 100000) := by
  exact
    packedTile8192 42651904 42668288 11 950 6530 25 _ _ (1756857 / 100000) (87843 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42668288 :
    ThetaLowerSegment 42668288 42684672 (4266073292823 / 100000) (2133842182769 / 50000) := by
  exact
    packedTile8192 42668288 42684672 11 917 6532 25 _ _ (351379 / 20000) (878449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42684672 :
    ThetaLowerSegment 42684672 42701056 (2133842182769 / 50000) (26683272406 / 625) := by
  exact
    packedTile8192 42684672 42701056 11 933 6533 25 _ _ (878467 / 50000) (1756937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42701056 :
    ThetaLowerSegment 42701056 42717440 (26683272406 / 625) (1067744223903 / 25000) := by
  exact
    packedTile8192 42701056 42717440 11 941 6534 25 _ _ (439243 / 25000) (70279 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42717440 :
    ThetaLowerSegment 42717440 42733824 (1067744223903 / 25000) (2136283494831 / 50000) := by
  exact
    packedTile8192 42717440 42733824 11 905 6535 25 _ _ (175701 / 10000) (1757013 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42733824 :
    ThetaLowerSegment 42733824 42750208 (2136283494831 / 50000) (4274223886869 / 100000) := by
  exact
    packedTile8192 42733824 42750208 11 943 6537 25 _ _ (1757049 / 100000) (439263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42750208 :
    ThetaLowerSegment 42750208 42766592 (4274223886869 / 100000) (2137933381607 / 50000) := by
  exact
    packedTile8192 42750208 42766592 11 935 6538 25 _ _ (1757087 / 100000) (175709 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42766592 :
    ThetaLowerSegment 42766592 42782976 (2137933381607 / 50000) (534687611183 / 12500) := by
  exact
    packedTile8192 42766592 42782976 11 930 6539 25 _ _ (14057 / 800) (219641 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42782976 :
    ThetaLowerSegment 42782976 42799360 (534687611183 / 12500) (133723629311 / 3125) := by
  exact
    packedTile8192 42782976 42799360 11 942 6540 25 _ _ (439291 / 25000) (1757167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42799360 :
    ThetaLowerSegment 42799360 42815744 (133723629311 / 3125) (267551812141 / 6250) := by
  exact
    packedTile8192 42799360 42815744 11 952 6542 25 _ _ (878601 / 50000) (351441 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42815744 :
    ThetaLowerSegment 42815744 42832128 (267551812141 / 6250) (535302851367 / 12500) := by
  exact
    packedTile8192 42815744 42832128 11 907 6543 25 _ _ (43931 / 2500) (1757243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42832128 :
    ThetaLowerSegment 42832128 42848512 (535302851367 / 12500) (267753787127 / 6250) := by
  exact
    packedTile8192 42832128 42848512 11 932 6544 25 _ _ (878639 / 50000) (1757281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42848512 :
    ThetaLowerSegment 42848512 42864896 (267753787127 / 6250) (1071428118003 / 25000) := by
  exact
    packedTile8192 42848512 42864896 11 940 6545 25 _ _ (1757317 / 100000) (43933 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42864896 :
    ThetaLowerSegment 42864896 42881280 (1071428118003 / 25000) (4287306392997 / 100000) := by
  exact
    packedTile8192 42864896 42881280 11 907 6547 25 _ _ (351471 / 20000) (878679 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42881280 :
    ThetaLowerSegment 42881280 42897664 (4287306392997 / 100000) (4288877502339 / 100000) := by
  exact
    packedTile8192 42881280 42897664 11 894 6548 25 _ _ (1757393 / 100000) (439349 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42897664 :
    ThetaLowerSegment 42897664 42914048 (4288877502339 / 100000) (4290494338859 / 100000) := by
  exact
    packedTile8192 42897664 42914048 11 920 6549 25 _ _ (1757431 / 100000) (878717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42914048 :
    ThetaLowerSegment 42914048 42930432 (4290494338859 / 100000) (2146068786187 / 50000) := by
  exact
    packedTile8192 42914048 42930432 11 935 6550 25 _ _ (1757469 / 100000) (54921 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42930432 :
    ThetaLowerSegment 42930432 42946816 (2146068786187 / 50000) (429381071999 / 10000) := by
  exact
    packedTile8192 42930432 42946816 11 952 6552 25 _ _ (439377 / 25000) (1757511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42946816 :
    ThetaLowerSegment 42946816 42963200 (429381071999 / 10000) (2147706800971 / 50000) := by
  exact
    packedTile8192 42946816 42963200 11 912 6553 25 _ _ (878773 / 50000) (1757549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42963200 :
    ThetaLowerSegment 42963200 42979584 (2147706800971 / 50000) (2148505622899 / 50000) := by
  exact
    packedTile8192 42963200 42979584 11 909 6554 25 _ _ (109849 / 6250) (1757587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42979584 :
    ThetaLowerSegment 42979584 42995968 (2148505622899 / 50000) (2149326432373 / 50000) := by
  exact
    packedTile8192 42979584 42995968 11 934 6555 25 _ _ (878811 / 50000) (14061 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell42995968 :
    ThetaLowerSegment 42995968 43012352 (2149326432373 / 50000) (2150126167673 / 50000) := by
  exact
    packedTile8192 42995968 43012352 11 910 6557 25 _ _ (87883 / 5000) (1757663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43012352 :
    ThetaLowerSegment 43012352 43028736 (2150126167673 / 50000) (430186590211 / 10000) := by
  exact
    packedTile8192 43012352 43028736 11 918 6558 25 _ _ (878849 / 50000) (1757701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43028736 :
    ThetaLowerSegment 43028736 43045120 (430186590211 / 10000) (430352696263 / 10000) := by
  exact
    packedTile8192 43028736 43045120 11 945 6559 25 _ _ (219717 / 12500) (1757739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43045120 :
    ThetaLowerSegment 43045120 43061504 (430352696263 / 10000) (2152568541807 / 50000) := by
  exact
    packedTile8192 43045120 43061504 11 916 6560 25 _ _ (878887 / 50000) (1757777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43061504 :
    ThetaLowerSegment 43061504 43077888 (2152568541807 / 50000) (2153392076729 / 50000) := by
  exact
    packedTile8192 43061504 43077888 11 937 6562 25 _ _ (439453 / 25000) (351563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43077888 :
    ThetaLowerSegment 43077888 43094272 (2153392076729 / 50000) (134640289654 / 3125) := by
  exact
    packedTile8192 43077888 43094272 11 970 6563 25 _ _ (1757851 / 100000) (878927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43094272 :
    ThetaLowerSegment 43094272 43110656 (134640289654 / 3125) (862029391651 / 20000) := by
  exact
    packedTile8192 43094272 43110656 11 943 6564 25 _ _ (1757889 / 100000) (439473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43110656 :
    ThetaLowerSegment 43110656 43127040 (862029391651 / 20000) (4311760735241 / 100000) := by
  exact
    packedTile8192 43110656 43127040 11 918 6565 25 _ _ (1757927 / 100000) (175793 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43127040 :
    ThetaLowerSegment 43127040 43143424 (4311760735241 / 100000) (4313381578971 / 100000) := by
  exact
    packedTile8192 43127040 43143424 11 922 6567 25 _ _ (351593 / 20000) (109873 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43143424 :
    ThetaLowerSegment 43143424 43159808 (4313381578971 / 100000) (2157524961909 / 50000) := by
  exact
    packedTile8192 43143424 43159808 11 949 6568 25 _ _ (1758003 / 100000) (879003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43159808 :
    ThetaLowerSegment 43159808 43176192 (2157524961909 / 50000) (2158351241179 / 50000) := by
  exact
    packedTile8192 43159808 43176192 11 940 6569 25 _ _ (1758041 / 100000) (439511 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43176192 :
    ThetaLowerSegment 43176192 43192576 (2158351241179 / 50000) (431832694643 / 10000) := by
  exact
    packedTile8192 43176192 43192576 11 924 6570 25 _ _ (879039 / 50000) (1758081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43192576 :
    ThetaLowerSegment 43192576 43208960 (431832694643 / 10000) (2159988029619 / 50000) := by
  exact
    packedTile8192 43192576 43208960 11 938 6572 25 _ _ (439529 / 25000) (1758119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43208960 :
    ThetaLowerSegment 43208960 43225344 (2159988029619 / 50000) (2160809087537 / 50000) := by
  exact
    packedTile8192 43208960 43225344 11 934 6573 25 _ _ (879077 / 50000) (1758157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43225344 :
    ThetaLowerSegment 43225344 43241728 (2160809087537 / 50000) (2161623130433 / 50000) := by
  exact
    packedTile8192 43225344 43241728 11 926 6574 25 _ _ (109887 / 6250) (351639 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43241728 :
    ThetaLowerSegment 43241728 43258112 (2161623130433 / 50000) (540608198837 / 12500) := by
  exact
    packedTile8192 43241728 43258112 11 921 6575 25 _ _ (175823 / 10000) (1758233 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43258112 :
    ThetaLowerSegment 43258112 43274496 (540608198837 / 12500) (270404100911 / 6250) := by
  exact
    packedTile8192 43258112 43274496 11 910 6577 25 _ _ (439567 / 25000) (1758271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43274496 :
    ThetaLowerSegment 43274496 43290880 (270404100911 / 6250) (2164061848567 / 50000) := by
  exact
    packedTile8192 43274496 43290880 11 943 6578 25 _ _ (879153 / 50000) (1758309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43290880 :
    ThetaLowerSegment 43290880 43307264 (2164061848567 / 50000) (432976599043 / 10000) := by
  exact
    packedTile8192 43290880 43307264 11 934 6579 25 _ _ (219793 / 12500) (1758347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43307264 :
    ThetaLowerSegment 43307264 43323648 (432976599043 / 10000) (2165693609317 / 50000) := by
  exact
    packedTile8192 43307264 43323648 11 922 6580 25 _ _ (879191 / 50000) (351677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43323648 :
    ThetaLowerSegment 43323648 43340032 (2165693609317 / 50000) (1083253878657 / 25000) := by
  exact
    packedTile8192 43323648 43340032 11 926 6582 25 _ _ (1758419 / 100000) (879211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43340032 :
    ThetaLowerSegment 43340032 43356416 (1083253878657 / 25000) (4334726493289 / 100000) := by
  exact
    packedTile8192 43340032 43356416 11 973 6583 25 _ _ (1758457 / 100000) (87923 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43356416 :
    ThetaLowerSegment 43356416 43372800 (4334726493289 / 100000) (542037982913 / 12500) := by
  exact
    packedTile8192 43356416 43372800 11 897 6584 25 _ _ (351699 / 20000) (879249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43372800 :
    ThetaLowerSegment 43372800 43389184 (542037982913 / 12500) (4337962159923 / 100000) := by
  exact
    packedTile8192 43372800 43389184 11 943 6585 25 _ _ (1758533 / 100000) (219817 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43389184 :
    ThetaLowerSegment 43389184 43405568 (4337962159923 / 100000) (4339611699521 / 100000) := by
  exact
    packedTile8192 43389184 43405568 11 938 6587 25 _ _ (1758571 / 100000) (879287 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43405568 :
    ThetaLowerSegment 43405568 43421952 (4339611699521 / 100000) (4341271825473 / 100000) := by
  exact
    packedTile8192 43405568 43421952 11 944 6588 25 _ _ (109913 / 6250) (1758611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43421952 :
    ThetaLowerSegment 43421952 43438336 (4341271825473 / 100000) (4342886262501 / 100000) := by
  exact
    packedTile8192 43421952 43438336 11 918 6589 25 _ _ (879323 / 50000) (1758649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43438336 :
    ThetaLowerSegment 43438336 43454720 (4342886262501 / 100000) (4344569323089 / 100000) := by
  exact
    packedTile8192 43438336 43454720 11 957 6590 25 _ _ (439671 / 25000) (1758687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43454720 :
    ThetaLowerSegment 43454720 43471104 (4344569323089 / 100000) (4346189106051 / 100000) := by
  exact
    packedTile8192 43454720 43471104 11 921 6592 25 _ _ (879361 / 50000) (70349 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43471104 :
    ThetaLowerSegment 43471104 43487488 (4346189106051 / 100000) (4347824751921 / 100000) := by
  exact
    packedTile8192 43471104 43487488 11 930 6593 25 _ _ (1758759 / 100000) (879381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43487488 :
    ThetaLowerSegment 43487488 43503872 (4347824751921 / 100000) (4349506161853 / 100000) := by
  exact
    packedTile8192 43487488 43503872 11 956 6594 25 _ _ (1758797 / 100000) (4397 / 250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43503872 :
    ThetaLowerSegment 43503872 43520256 (4349506161853 / 100000) (4351120772383 / 100000) := by
  exact
    packedTile8192 43503872 43520256 11 918 6595 25 _ _ (351767 / 20000) (879419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43520256 :
    ThetaLowerSegment 43520256 43536640 (4351120772383 / 100000) (4352789941911 / 100000) := by
  exact
    packedTile8192 43520256 43536640 11 949 6596 25 _ _ (219859 / 12500) (14071 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43536640 :
    ThetaLowerSegment 43536640 43553024 (4352789941911 / 100000) (4354459147501 / 100000) := by
  exact
    packedTile8192 43536640 43553024 11 949 6598 25 _ _ (175891 / 10000) (1758913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43553024 :
    ThetaLowerSegment 43553024 43569408 (4354459147501 / 100000) (435612487031 / 10000) := by
  exact
    packedTile8192 43553024 43569408 11 947 6599 25 _ _ (1758947 / 100000) (35179 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43569408 :
    ThetaLowerSegment 43569408 43585792 (435612487031 / 10000) (435777128027 / 10000) := by
  exact
    packedTile8192 43569408 43585792 11 936 6600 25 _ _ (351797 / 20000) (439747 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43585792 :
    ThetaLowerSegment 43585792 43602176 (435777128027 / 10000) (2179687754623 / 50000) := by
  exact
    packedTile8192 43585792 43602176 11 912 6601 25 _ _ (1759023 / 100000) (879513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43602176 :
    ThetaLowerSegment 43602176 43618560 (2179687754623 / 50000) (2180481090683 / 50000) := by
  exact
    packedTile8192 43602176 43618560 11 902 6603 25 _ _ (87953 / 5000) (1759063 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43618560 :
    ThetaLowerSegment 43618560 43634944 (2180481090683 / 50000) (2181302589449 / 50000) := by
  exact
    packedTile8192 43618560 43634944 11 934 6604 25 _ _ (879549 / 50000) (1759101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43634944 :
    ThetaLowerSegment 43634944 43651328 (2181302589449 / 50000) (2182108273279 / 50000) := by
  exact
    packedTile8192 43634944 43651328 11 916 6605 25 _ _ (351827 / 20000) (879569 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43651328 :
    ThetaLowerSegment 43651328 43667712 (2182108273279 / 50000) (136430694079 / 3125) := by
  exact
    packedTile8192 43651328 43667712 11 890 6606 25 _ _ (1759173 / 100000) (219897 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43667712 :
    ThetaLowerSegment 43667712 43684096 (136430694079 / 3125) (2183718813569 / 50000) := by
  exact
    packedTile8192 43667712 43684096 11 941 6608 25 _ _ (175921 / 10000) (1759213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43684096 :
    ThetaLowerSegment 43684096 43700480 (2183718813569 / 50000) (2184517512161 / 50000) := by
  exact
    packedTile8192 43684096 43700480 11 908 6609 25 _ _ (109953 / 6250) (1759251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43700480 :
    ThetaLowerSegment 43700480 43716864 (2184517512161 / 50000) (1092671308413 / 25000) := by
  exact
    packedTile8192 43700480 43716864 11 938 6610 25 _ _ (351857 / 20000) (219911 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43716864 :
    ThetaLowerSegment 43716864 43733248 (1092671308413 / 25000) (874464632673 / 20000) := by
  exact
    packedTile8192 43716864 43733248 11 931 6611 25 _ _ (1759323 / 100000) (879663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43733248 :
    ThetaLowerSegment 43733248 43749632 (874464632673 / 20000) (874785891809 / 20000) := by
  exact
    packedTile8192 43733248 43749632 11 913 6613 25 _ _ (10996 / 625) (1759363 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43749632 :
    ThetaLowerSegment 43749632 43766016 (874785891809 / 20000) (4375607924737 / 100000) := by
  exact
    packedTile8192 43749632 43766016 11 954 6614 25 _ _ (879699 / 50000) (1759401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43766016 :
    ThetaLowerSegment 43766016 43782400 (4375607924737 / 100000) (4377226604937 / 100000) := by
  exact
    packedTile8192 43766016 43782400 11 920 6615 25 _ _ (351887 / 20000) (879719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43782400 :
    ThetaLowerSegment 43782400 43798784 (4377226604937 / 100000) (4378884028503 / 100000) := by
  exact
    packedTile8192 43782400 43798784 11 942 6616 25 _ _ (1759473 / 100000) (439869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43798784 :
    ThetaLowerSegment 43798784 43815168 (4378884028503 / 100000) (4380471106523 / 100000) := by
  exact
    packedTile8192 43798784 43815168 11 902 6618 25 _ _ (175951 / 10000) (1759513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43815168 :
    ThetaLowerSegment 43815168 43831552 (4380471106523 / 100000) (4382139158027 / 100000) := by
  exact
    packedTile8192 43815168 43831552 11 948 6619 25 _ _ (439887 / 25000) (1759551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43831552 :
    ThetaLowerSegment 43831552 43847936 (4382139158027 / 100000) (2191881627491 / 50000) := by
  exact
    packedTile8192 43831552 43847936 11 923 6620 25 _ _ (351917 / 20000) (439897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43847936 :
    ThetaLowerSegment 43847936 43864320 (2191881627491 / 50000) (2192722726807 / 50000) := by
  exact
    packedTile8192 43847936 43864320 11 956 6621 25 _ _ (879811 / 50000) (14077 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43864320 :
    ThetaLowerSegment 43864320 43880704 (2192722726807 / 50000) (2193522492277 / 50000) := by
  exact
    packedTile8192 43864320 43880704 11 909 6623 25 _ _ (87983 / 5000) (1759663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43880704 :
    ThetaLowerSegment 43880704 43897088 (2193522492277 / 50000) (1097163336903 / 25000) := by
  exact
    packedTile8192 43880704 43897088 11 914 6624 25 _ _ (1759697 / 100000) (17597 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43897088 :
    ThetaLowerSegment 43897088 43913472 (1097163336903 / 25000) (2195128232643 / 50000) := by
  exact
    packedTile8192 43897088 43913472 11 911 6625 25 _ _ (879867 / 50000) (1759737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43913472 :
    ThetaLowerSegment 43913472 43929856 (2195128232643 / 50000) (2195936847877 / 50000) := by
  exact
    packedTile8192 43913472 43929856 11 919 6626 25 _ _ (439943 / 25000) (70391 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43929856 :
    ThetaLowerSegment 43929856 43946240 (2195936847877 / 50000) (439357015163 / 10000) := by
  exact
    packedTile8192 43929856 43946240 11 964 6627 25 _ _ (1759809 / 100000) (439953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43946240 :
    ThetaLowerSegment 43946240 43962624 (439357015163 / 10000) (2197645640509 / 50000) := by
  exact
    packedTile8192 43946240 43962624 11 978 6629 25 _ _ (879923 / 50000) (1759849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43962624 :
    ThetaLowerSegment 43962624 43979008 (2197645640509 / 50000) (2198476305757 / 50000) := by
  exact
    packedTile8192 43962624 43979008 11 944 6630 25 _ _ (439971 / 25000) (1759887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43979008 :
    ThetaLowerSegment 43979008 43995392 (2198476305757 / 50000) (4398615736859 / 100000) := by
  exact
    packedTile8192 43979008 43995392 11 945 6631 25 _ _ (1759921 / 100000) (439981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell43995392 :
    ThetaLowerSegment 43995392 44011776 (4398615736859 / 100000) (4400226098429 / 100000) := by
  exact
    packedTile8192 43995392 44011776 11 915 6632 25 _ _ (879979 / 50000) (1759961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44011776 :
    ThetaLowerSegment 44011776 44028160 (4400226098429 / 100000) (4401820653899 / 100000) := by
  exact
    packedTile8192 44011776 44028160 11 906 6634 25 _ _ (351999 / 20000) (879999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44028160 :
    ThetaLowerSegment 44028160 44044544 (4401820653899 / 100000) (4403501484459 / 100000) := by
  exact
    packedTile8192 44028160 44044544 11 955 6635 25 _ _ (55001 / 3125) (352007 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44044544 :
    ThetaLowerSegment 44044544 44060928 (4403501484459 / 100000) (4405147149909 / 100000) := by
  exact
    packedTile8192 44044544 44060928 11 935 6636 25 _ _ (176007 / 10000) (1760073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44060928 :
    ThetaLowerSegment 44060928 44077312 (4405147149909 / 100000) (176271925211 / 4000) := by
  exact
    packedTile8192 44060928 44077312 11 938 6637 25 _ _ (1760107 / 100000) (176011 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44077312 :
    ThetaLowerSegment 44077312 44093696 (176271925211 / 4000) (4408380499731 / 100000) := by
  exact
    packedTile8192 44077312 44093696 11 899 6639 25 _ _ (110009 / 6250) (1760147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44093696 :
    ThetaLowerSegment 44093696 44110080 (4408380499731 / 100000) (4410003386613 / 100000) := by
  exact
    packedTile8192 44093696 44110080 11 922 6640 25 _ _ (1760181 / 100000) (220023 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44110080 :
    ThetaLowerSegment 44110080 44126464 (4410003386613 / 100000) (4411605184993 / 100000) := by
  exact
    packedTile8192 44110080 44126464 11 910 6641 25 _ _ (880109 / 50000) (1760221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44126464 :
    ThetaLowerSegment 44126464 44142848 (4411605184993 / 100000) (4413242223073 / 100000) := by
  exact
    packedTile8192 44126464 44142848 11 930 6642 25 _ _ (55008 / 3125) (1760259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44142848 :
    ThetaLowerSegment 44142848 44159232 (4413242223073 / 100000) (275930065991 / 6250) := by
  exact
    packedTile8192 44142848 44159232 11 931 6644 25 _ _ (1760293 / 100000) (220037 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44159232 :
    ThetaLowerSegment 44159232 44175616 (275930065991 / 6250) (2208252920223 / 50000) := by
  exact
    packedTile8192 44159232 44175616 11 923 6645 25 _ _ (176033 / 10000) (1760333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44175616 :
    ThetaLowerSegment 44175616 44192000 (2208252920223 / 50000) (4418144742123 / 100000) := by
  exact
    packedTile8192 44175616 44192000 11 931 6646 25 _ _ (1760367 / 100000) (176037 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44192000 :
    ThetaLowerSegment 44192000 44208384 (4418144742123 / 100000) (4419829448751 / 100000) := by
  exact
    packedTile8192 44192000 44208384 11 957 6647 25 _ _ (440101 / 25000) (1760407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44208384 :
    ThetaLowerSegment 44208384 44224768 (4419829448751 / 100000) (4421445533589 / 100000) := by
  exact
    packedTile8192 44208384 44224768 11 918 6648 25 _ _ (1760441 / 100000) (440111 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44224768 :
    ThetaLowerSegment 44224768 44241152 (4421445533589 / 100000) (4423082778129 / 100000) := by
  exact
    packedTile8192 44224768 44241152 11 930 6650 25 _ _ (880239 / 50000) (1760481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44241152 :
    ThetaLowerSegment 44241152 44257536 (4423082778129 / 100000) (2212353866737 / 50000) := by
  exact
    packedTile8192 44241152 44257536 11 923 6651 25 _ _ (352103 / 20000) (880259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44257536 :
    ThetaLowerSegment 44257536 44273920 (2212353866737 / 50000) (2213196290869 / 50000) := by
  exact
    packedTile8192 44257536 44273920 11 957 6652 25 _ _ (220069 / 12500) (352111 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44273920 :
    ThetaLowerSegment 44273920 44290304 (2213196290869 / 50000) (1107021567089 / 25000) := by
  exact
    packedTile8192 44273920 44290304 11 962 6653 25 _ _ (1760589 / 100000) (110037 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44290304 :
    ThetaLowerSegment 44290304 44306688 (1107021567089 / 25000) (221485654339 / 5000) := by
  exact
    packedTile8192 44290304 44306688 11 924 6655 25 _ _ (880313 / 50000) (1760629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44306688 :
    ThetaLowerSegment 44306688 44323072 (221485654339 / 5000) (4431310008121 / 100000) := by
  exact
    packedTile8192 44306688 44323072 11 907 6656 25 _ _ (1760663 / 100000) (880333 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44323072 :
    ThetaLowerSegment 44323072 44339456 (4431310008121 / 100000) (4432966826821 / 100000) := by
  exact
    packedTile8192 44323072 44339456 11 941 6657 25 _ _ (17607 / 1000) (1760703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44339456 :
    ThetaLowerSegment 44339456 44355840 (4432966826821 / 100000) (2217280146903 / 50000) := by
  exact
    packedTile8192 44339456 44355840 11 905 6658 25 _ _ (1760737 / 100000) (88037 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44355840 :
    ThetaLowerSegment 44355840 44372224 (2217280146903 / 50000) (443620837827 / 10000) := by
  exact
    packedTile8192 44355840 44372224 11 936 6660 25 _ _ (880387 / 50000) (1760777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44372224 :
    ThetaLowerSegment 44372224 44388608 (443620837827 / 10000) (110945267907 / 2500) := by
  exact
    packedTile8192 44372224 44388608 11 910 6661 25 _ _ (1760811 / 100000) (880407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44388608 :
    ThetaLowerSegment 44388608 44404992 (110945267907 / 2500) (554930597903 / 12500) := by
  exact
    packedTile8192 44388608 44404992 11 928 6662 25 _ _ (110053 / 6250) (1760851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44404992 :
    ThetaLowerSegment 44404992 44421376 (554930597903 / 12500) (1110285569091 / 25000) := by
  exact
    packedTile8192 44404992 44421376 11 964 6663 25 _ _ (352177 / 20000) (220111 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44421376 :
    ThetaLowerSegment 44421376 44437760 (1110285569091 / 25000) (2221378520919 / 50000) := by
  exact
    packedTile8192 44421376 44437760 11 917 6664 25 _ _ (880461 / 50000) (70437 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44437760 :
    ThetaLowerSegment 44437760 44454144 (2221378520919 / 50000) (1111098683427 / 25000) := by
  exact
    packedTile8192 44437760 44454144 11 930 6666 25 _ _ (1760959 / 100000) (880481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44454144 :
    ThetaLowerSegment 44454144 44470528 (1111098683427 / 25000) (2223019751519 / 50000) := by
  exact
    packedTile8192 44454144 44470528 11 934 6667 25 _ _ (352199 / 20000) (880499 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44470528 :
    ThetaLowerSegment 44470528 44486912 (2223019751519 / 50000) (444767021867 / 10000) := by
  exact
    packedTile8192 44470528 44486912 11 926 6668 25 _ _ (220129 / 12500) (352207 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44486912 :
    ThetaLowerSegment 44486912 44503296 (444767021867 / 10000) (4449295685357 / 100000) := by
  exact
    packedTile8192 44486912 44503296 11 923 6669 25 _ _ (1761069 / 100000) (110067 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44503296 :
    ThetaLowerSegment 44503296 44519680 (4449295685357 / 100000) (4450910619559 / 100000) := by
  exact
    packedTile8192 44503296 44519680 11 917 6671 25 _ _ (880553 / 50000) (1761109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44519680 :
    ThetaLowerSegment 44519680 44536064 (4450910619559 / 100000) (2226290972133 / 50000) := by
  exact
    packedTile8192 44519680 44536064 11 949 6672 25 _ _ (1761143 / 100000) (880573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44536064 :
    ThetaLowerSegment 44536064 44552448 (2226290972133 / 50000) (556775718913 / 12500) := by
  exact
    packedTile8192 44536064 44552448 11 922 6673 25 _ _ (1761179 / 100000) (880591 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44552448 :
    ThetaLowerSegment 44552448 44568832 (556775718913 / 12500) (556982661793 / 12500) := by
  exact
    packedTile8192 44552448 44568832 11 940 6674 25 _ _ (55038 / 3125) (1761219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44568832 :
    ThetaLowerSegment 44568832 44585216 (556982661793 / 12500) (4457522155923 / 100000) := by
  exact
    packedTile8192 44568832 44585216 11 943 6675 25 _ _ (1761253 / 100000) (220157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44585216 :
    ThetaLowerSegment 44585216 44601600 (4457522155923 / 100000) (4459198904003 / 100000) := by
  exact
    packedTile8192 44585216 44601600 11 952 6677 25 _ _ (176129 / 10000) (1761293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44601600 :
    ThetaLowerSegment 44601600 44617984 (4459198904003 / 100000) (4460889777923 / 100000) := by
  exact
    packedTile8192 44601600 44617984 11 960 6678 25 _ _ (1761327 / 100000) (176133 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44617984 :
    ThetaLowerSegment 44617984 44634368 (4460889777923 / 100000) (892492887289 / 20000) := by
  exact
    packedTile8192 44617984 44634368 11 894 6679 25 _ _ (1761363 / 100000) (880683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44634368 :
    ThetaLowerSegment 44634368 44650752 (892492887289 / 20000) (892826496449 / 20000) := by
  exact
    packedTile8192 44634368 44650752 11 947 6680 25 _ _ (8807 / 500) (1761403 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44650752 :
    ThetaLowerSegment 44650752 44667136 (892826496449 / 20000) (4465742435663 / 100000) := by
  exact
    packedTile8192 44650752 44667136 11 914 6682 25 _ _ (1761437 / 100000) (11009 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44667136 :
    ThetaLowerSegment 44667136 44683520 (4465742435663 / 100000) (893477530289 / 20000) := by
  exact
    packedTile8192 44667136 44683520 11 934 6683 25 _ _ (1761473 / 100000) (440369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44683520 :
    ThetaLowerSegment 44683520 44699904 (893477530289 / 20000) (178763007121 / 4000) := by
  exact
    packedTile8192 44683520 44699904 11 958 6684 25 _ _ (176151 / 10000) (1761513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44699904 :
    ThetaLowerSegment 44699904 44716288 (178763007121 / 4000) (1117677913797 / 25000) := by
  exact
    packedTile8192 44699904 44716288 11 929 6685 25 _ _ (1761547 / 100000) (35231 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44716288 :
    ThetaLowerSegment 44716288 44732672 (1117677913797 / 25000) (2236174963689 / 50000) := by
  exact
    packedTile8192 44716288 44732672 11 930 6687 25 _ _ (1761583 / 100000) (880793 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44732672 :
    ThetaLowerSegment 44732672 44749056 (2236174963689 / 50000) (2236990593749 / 50000) := by
  exact
    packedTile8192 44732672 44749056 11 926 6688 25 _ _ (88081 / 5000) (1761623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44749056 :
    ThetaLowerSegment 44749056 44765440 (2236990593749 / 50000) (2237853805679 / 50000) := by
  exact
    packedTile8192 44749056 44765440 11 980 6689 25 _ _ (1761657 / 100000) (88083 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44765440 :
    ThetaLowerSegment 44765440 44781824 (2237853805679 / 50000) (4477298420137 / 100000) := by
  exact
    packedTile8192 44765440 44781824 11 903 6690 25 _ _ (1761693 / 100000) (55053 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44781824 :
    ThetaLowerSegment 44781824 44798208 (4477298420137 / 100000) (4478961493257 / 100000) := by
  exact
    packedTile8192 44781824 44798208 11 944 6691 25 _ _ (176173 / 10000) (1761733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44798208 :
    ThetaLowerSegment 44798208 44814592 (4478961493257 / 100000) (4480541797359 / 100000) := by
  exact
    packedTile8192 44798208 44814592 11 897 6693 25 _ _ (880883 / 50000) (1761769 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44814592 :
    ThetaLowerSegment 44814592 44830976 (4480541797359 / 100000) (4482190844967 / 100000) := by
  exact
    packedTile8192 44814592 44830976 11 936 6694 25 _ _ (1761803 / 100000) (880903 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44830976 :
    ThetaLowerSegment 44830976 44847360 (4482190844967 / 100000) (4483783547423 / 100000) := by
  exact
    packedTile8192 44830976 44847360 11 904 6695 25 _ _ (1761839 / 100000) (880921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44847360 :
    ThetaLowerSegment 44847360 44863744 (4483783547423 / 100000) (35883686827 / 800) := by
  exact
    packedTile8192 44847360 44863744 11 952 6696 25 _ _ (440469 / 25000) (1761879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44863744 :
    ThetaLowerSegment 44863744 44880128 (35883686827 / 800) (2243550597189 / 50000) := by
  exact
    packedTile8192 44863744 44880128 11 931 6698 25 _ _ (1761913 / 100000) (440479 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44880128 :
    ThetaLowerSegment 44880128 44896512 (2243550597189 / 50000) (4488699282121 / 100000) := by
  exact
    packedTile8192 44880128 44896512 11 907 6699 25 _ _ (1761949 / 100000) (55061 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44896512 :
    ThetaLowerSegment 44896512 44912896 (4488699282121 / 100000) (4490352024989 / 100000) := by
  exact
    packedTile8192 44896512 44912896 11 938 6700 25 _ _ (880993 / 50000) (1761989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44912896 :
    ThetaLowerSegment 44912896 44929280 (4490352024989 / 100000) (4491966037141 / 100000) := by
  exact
    packedTile8192 44912896 44929280 11 916 6701 25 _ _ (881011 / 50000) (70481 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44929280 :
    ThetaLowerSegment 44929280 44945664 (4491966037141 / 100000) (2246796208799 / 50000) := by
  exact
    packedTile8192 44929280 44945664 11 923 6702 25 _ _ (1762059 / 100000) (881031 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44945664 :
    ThetaLowerSegment 44945664 44962048 (2246796208799 / 50000) (4495289315083 / 100000) := by
  exact
    packedTile8192 44945664 44962048 11 963 6704 25 _ _ (352419 / 20000) (881049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44962048 :
    ThetaLowerSegment 44962048 44978432 (4495289315083 / 100000) (4496910475603 / 100000) := by
  exact
    packedTile8192 44962048 44978432 11 920 6705 25 _ _ (1762131 / 100000) (881067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44978432 :
    ThetaLowerSegment 44978432 44994816 (4496910475603 / 100000) (899713030271 / 20000) := by
  exact
    packedTile8192 44978432 44994816 11 939 6706 25 _ _ (220271 / 12500) (1762171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell44994816 :
    ThetaLowerSegment 44994816 45011200 (899713030271 / 20000) (4500170519199 / 100000) := by
  exact
    packedTile8192 44994816 45011200 11 911 6707 25 _ _ (440551 / 25000) (1762207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45011200 :
    ThetaLowerSegment 45011200 45027584 (4500170519199 / 100000) (2250909107267 / 50000) := by
  exact
    packedTile8192 45011200 45027584 11 935 6709 25 _ _ (1762241 / 100000) (440561 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45027584 :
    ThetaLowerSegment 45027584 45043968 (2250909107267 / 50000) (450345360759 / 10000) := by
  exact
    packedTile8192 45027584 45043968 11 928 6710 25 _ _ (1762277 / 100000) (44057 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45043968 :
    ThetaLowerSegment 45043968 45060352 (450345360759 / 10000) (4505161288887 / 100000) := by
  exact
    packedTile8192 45043968 45060352 11 969 6711 25 _ _ (1762313 / 100000) (440579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45060352 :
    ThetaLowerSegment 45060352 45076736 (4505161288887 / 100000) (4506828471987 / 100000) := by
  exact
    packedTile8192 45060352 45076736 11 946 6712 25 _ _ (35247 / 2000) (1762353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45076736 :
    ThetaLowerSegment 45076736 45093120 (4506828471987 / 100000) (4508439292791 / 100000) := by
  exact
    packedTile8192 45076736 45093120 11 914 6713 25 _ _ (881193 / 50000) (1762389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45093120 :
    ThetaLowerSegment 45093120 45109504 (4508439292791 / 100000) (2255034767033 / 50000) := by
  exact
    packedTile8192 45093120 45109504 11 925 6715 25 _ _ (1762423 / 100000) (881213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45109504 :
    ThetaLowerSegment 45109504 45125888 (2255034767033 / 50000) (4511717433231 / 100000) := by
  exact
    packedTile8192 45109504 45125888 11 935 6716 25 _ _ (1762459 / 100000) (881231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45125888 :
    ThetaLowerSegment 45125888 45142272 (4511717433231 / 100000) (1128339579019 / 25000) := by
  exact
    packedTile8192 45125888 45142272 11 931 6717 25 _ _ (352499 / 20000) (881249 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45142272 :
    ThetaLowerSegment 45142272 45158656 (1128339579019 / 25000) (4514949881569 / 100000) := by
  exact
    packedTile8192 45142272 45158656 11 903 6718 25 _ _ (1762531 / 100000) (881267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45158656 :
    ThetaLowerSegment 45158656 45175040 (4514949881569 / 100000) (4516550293313 / 100000) := by
  exact
    packedTile8192 45158656 45175040 11 908 6720 25 _ _ (220321 / 12500) (1762571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45175040 :
    ThetaLowerSegment 45175040 45191424 (4516550293313 / 100000) (4518207141073 / 100000) := by
  exact
    packedTile8192 45175040 45191424 11 940 6721 25 _ _ (440651 / 25000) (1762607 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45191424 :
    ThetaLowerSegment 45191424 45207808 (4518207141073 / 100000) (4519823481953 / 100000) := by
  exact
    packedTile8192 45191424 45207808 11 917 6722 25 _ _ (22033 / 1250) (1762643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45207808 :
    ThetaLowerSegment 45207808 45224192 (4519823481953 / 100000) (4521501550457 / 100000) := by
  exact
    packedTile8192 45207808 45224192 11 952 6723 25 _ _ (1762677 / 100000) (44067 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45224192 :
    ThetaLowerSegment 45224192 45240576 (4521501550457 / 100000) (4523165551529 / 100000) := by
  exact
    packedTile8192 45224192 45240576 11 944 6724 25 _ _ (1762713 / 100000) (440679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45240576 :
    ThetaLowerSegment 45240576 45256960 (4523165551529 / 100000) (4524826061087 / 100000) := by
  exact
    packedTile8192 45240576 45256960 11 942 6726 25 _ _ (1762749 / 100000) (55086 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45256960 :
    ThetaLowerSegment 45256960 45273344 (4524826061087 / 100000) (2263230081391 / 50000) := by
  exact
    packedTile8192 45256960 45273344 11 927 6727 25 _ _ (352557 / 20000) (440697 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45273344 :
    ThetaLowerSegment 45273344 45289728 (2263230081391 / 50000) (45281489453 / 1000) := by
  exact
    packedTile8192 45273344 45289728 11 958 6728 25 _ _ (1762821 / 100000) (220353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45289728 :
    ThetaLowerSegment 45289728 45306112 (45281489453 / 1000) (90595591779 / 2000) := by
  exact
    packedTile8192 45289728 45306112 11 925 6729 25 _ _ (881429 / 50000) (1762861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45306112 :
    ThetaLowerSegment 45306112 45322496 (90595591779 / 2000) (2265739509383 / 50000) := by
  exact
    packedTile8192 45306112 45322496 11 964 6730 25 _ _ (881447 / 50000) (1762897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45322496 :
    ThetaLowerSegment 45322496 45338880 (2265739509383 / 50000) (2266552220113 / 50000) := by
  exact
    packedTile8192 45322496 45338880 11 922 6732 25 _ _ (176293 / 10000) (1762933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45338880 :
    ThetaLowerSegment 45338880 45355264 (2266552220113 / 50000) (2267407258623 / 50000) := by
  exact
    packedTile8192 45338880 45355264 11 970 6733 25 _ _ (881483 / 50000) (1762969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45355264 :
    ThetaLowerSegment 45355264 45371648 (2267407258623 / 50000) (2268232343559 / 50000) := by
  exact
    packedTile8192 45355264 45371648 11 936 6734 25 _ _ (881501 / 50000) (352601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45371648 :
    ThetaLowerSegment 45371648 45388032 (2268232343559 / 50000) (226903364433 / 5000) := by
  exact
    packedTile8192 45371648 45388032 11 909 6735 25 _ _ (881519 / 50000) (1763041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45388032 :
    ThetaLowerSegment 45388032 45404416 (226903364433 / 5000) (90794315257 / 2000) := by
  exact
    packedTile8192 45388032 45404416 11 935 6737 25 _ _ (881537 / 50000) (1763077 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45404416 :
    ThetaLowerSegment 45404416 45420800 (90794315257 / 2000) (454129903563 / 10000) := by
  exact
    packedTile8192 45404416 45420800 11 898 6738 25 _ _ (176311 / 10000) (1763113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45420800 :
    ThetaLowerSegment 45420800 45437184 (454129903563 / 10000) (4542979314721 / 100000) := by
  exact
    packedTile8192 45420800 45437184 11 953 6739 25 _ _ (1763147 / 100000) (35263 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45437184 :
    ThetaLowerSegment 45437184 45453568 (4542979314721 / 100000) (1136166670213 / 25000) := by
  exact
    packedTile8192 45437184 45453568 11 957 6740 25 _ _ (1763183 / 100000) (881593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45453568 :
    ThetaLowerSegment 45453568 45469952 (1136166670213 / 25000) (4546350554997 / 100000) := by
  exact
    packedTile8192 45453568 45469952 11 955 6741 25 _ _ (1763219 / 100000) (881611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45469952 :
    ThetaLowerSegment 45469952 45486336 (4546350554997 / 100000) (4547983329127 / 100000) := by
  exact
    packedTile8192 45469952 45486336 11 926 6743 25 _ _ (352651 / 20000) (881629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45486336 :
    ThetaLowerSegment 45486336 45502720 (4547983329127 / 100000) (4549573817609 / 100000) := by
  exact
    packedTile8192 45486336 45502720 11 902 6744 25 _ _ (1763291 / 100000) (881647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45502720 :
    ThetaLowerSegment 45502720 45519104 (4549573817609 / 100000) (2275611264177 / 50000) := by
  exact
    packedTile8192 45502720 45519104 11 935 6745 25 _ _ (1763327 / 100000) (176333 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45519104 :
    ThetaLowerSegment 45519104 45535488 (2275611264177 / 50000) (4552881852937 / 100000) := by
  exact
    packedTile8192 45519104 45535488 11 941 6746 25 _ _ (1763363 / 100000) (881683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45535488 :
    ThetaLowerSegment 45535488 45551872 (4552881852937 / 100000) (455451652381 / 10000) := by
  exact
    packedTile8192 45535488 45551872 11 927 6747 25 _ _ (1763399 / 100000) (881701 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45551872 :
    ThetaLowerSegment 45551872 45568256 (455451652381 / 10000) (18224583751 / 400) := by
  exact
    packedTile8192 45551872 45568256 11 924 6749 25 _ _ (352687 / 20000) (881719 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45568256 :
    ThetaLowerSegment 45568256 45584640 (18224583751 / 400) (4557805363961 / 100000) := by
  exact
    packedTile8192 45568256 45584640 11 941 6750 25 _ _ (1763471 / 100000) (881737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45584640 :
    ThetaLowerSegment 45584640 45601024 (4557805363961 / 100000) (284966551503 / 6250) := by
  exact
    packedTile8192 45584640 45601024 11 941 6751 25 _ _ (1763507 / 100000) (176351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45601024 :
    ThetaLowerSegment 45601024 45617408 (284966551503 / 6250) (912227685271 / 20000) := by
  exact
    packedTile8192 45601024 45617408 11 949 6752 25 _ _ (1763543 / 100000) (881773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45617408 :
    ThetaLowerSegment 45617408 45633792 (912227685271 / 20000) (4562776790317 / 100000) := by
  exact
    packedTile8192 45617408 45633792 11 929 6754 25 _ _ (881789 / 50000) (1763581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45633792 :
    ThetaLowerSegment 45633792 45650176 (4562776790317 / 100000) (4564371097373 / 100000) := by
  exact
    packedTile8192 45633792 45650176 11 904 6755 25 _ _ (881807 / 50000) (1763617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45650176 :
    ThetaLowerSegment 45650176 45666560 (4564371097373 / 100000) (4566020110123 / 100000) := by
  exact
    packedTile8192 45650176 45666560 11 935 6756 25 _ _ (35273 / 2000) (1763653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45666560 :
    ThetaLowerSegment 45666560 45682944 (4566020110123 / 100000) (4567658574417 / 100000) := by
  exact
    packedTile8192 45666560 45682944 11 929 6757 25 _ _ (881843 / 50000) (1763689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45682944 :
    ThetaLowerSegment 45682944 45699328 (4567658574417 / 100000) (4569312945653 / 100000) := by
  exact
    packedTile8192 45682944 45699328 11 938 6758 25 _ _ (881861 / 50000) (70549 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45699328 :
    ThetaLowerSegment 45699328 45715712 (4569312945653 / 100000) (4570940894287 / 100000) := by
  exact
    packedTile8192 45699328 45715712 11 923 6760 25 _ _ (881879 / 50000) (1763761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45715712 :
    ThetaLowerSegment 45715712 45732096 (4570940894287 / 100000) (4572560057179 / 100000) := by
  exact
    packedTile8192 45715712 45732096 11 918 6761 25 _ _ (881897 / 50000) (1763797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45732096 :
    ThetaLowerSegment 45732096 45748480 (4572560057179 / 100000) (4574235695679 / 100000) := by
  exact
    packedTile8192 45732096 45748480 11 950 6762 25 _ _ (176383 / 10000) (1763833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45748480 :
    ThetaLowerSegment 45748480 45764864 (4574235695679 / 100000) (4575911367429 / 100000) := by
  exact
    packedTile8192 45748480 45764864 11 950 6763 25 _ _ (352773 / 20000) (440967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45764864 :
    ThetaLowerSegment 45764864 45781248 (4575911367429 / 100000) (4577565906567 / 100000) := by
  exact
    packedTile8192 45764864 45781248 11 938 6764 25 _ _ (1763901 / 100000) (55122 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45781248 :
    ThetaLowerSegment 45781248 45797632 (4577565906567 / 100000) (1144781747703 / 25000) := by
  exact
    packedTile8192 45781248 45797632 11 885 6766 25 _ _ (1763937 / 100000) (88197 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45797632 :
    ThetaLowerSegment 45797632 45814016 (1144781747703 / 25000) (4580719858431 / 100000) := by
  exact
    packedTile8192 45797632 45814016 11 903 6767 25 _ _ (1763973 / 100000) (220497 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45814016 :
    ThetaLowerSegment 45814016 45830400 (4580719858431 / 100000) (2291166963333 / 50000) := by
  exact
    packedTile8192 45814016 45830400 11 915 6768 25 _ _ (1764009 / 100000) (441003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45830400 :
    ThetaLowerSegment 45830400 45846784 (2291166963333 / 50000) (458399389207 / 10000) := by
  exact
    packedTile8192 45830400 45846784 11 941 6769 25 _ _ (441011 / 25000) (1764047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45846784 :
    ThetaLowerSegment 45846784 45863168 (458399389207 / 10000) (458564330687 / 10000) := by
  exact
    packedTile8192 45846784 45863168 11 935 6771 25 _ _ (22051 / 1250) (1764083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45863168 :
    ThetaLowerSegment 45863168 45879552 (458564330687 / 10000) (2293643731491 / 50000) := by
  exact
    packedTile8192 45863168 45879552 11 932 6772 25 _ _ (441029 / 25000) (1764119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45879552 :
    ThetaLowerSegment 45879552 45895936 (2293643731491 / 50000) (2294481703691 / 50000) := by
  exact
    packedTile8192 45879552 45895936 11 950 6773 25 _ _ (220519 / 12500) (352831 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45895936 :
    ThetaLowerSegment 45895936 45912320 (2294481703691 / 50000) (4590634092471 / 100000) := by
  exact
    packedTile8192 45895936 45912320 11 947 6774 25 _ _ (1764187 / 100000) (176419 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45912320 :
    ThetaLowerSegment 45912320 45928704 (4590634092471 / 100000) (4592320689659 / 100000) := by
  exact
    packedTile8192 45912320 45928704 11 956 6775 25 _ _ (1764223 / 100000) (882113 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45928704 :
    ThetaLowerSegment 45928704 45945088 (4592320689659 / 100000) (4593943807939 / 100000) := by
  exact
    packedTile8192 45928704 45945088 11 920 6777 25 _ _ (1764259 / 100000) (882131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45945088 :
    ThetaLowerSegment 45945088 45961472 (4593943807939 / 100000) (4595575779889 / 100000) := by
  exact
    packedTile8192 45945088 45961472 11 925 6778 25 _ _ (882147 / 50000) (1764297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45961472 :
    ThetaLowerSegment 45961472 45977856 (4595575779889 / 100000) (4597140740599 / 100000) := by
  exact
    packedTile8192 45961472 45977856 11 887 6779 25 _ _ (176433 / 10000) (1764333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45977856 :
    ThetaLowerSegment 45977856 45994240 (4597140740599 / 100000) (4598781600979 / 100000) := by
  exact
    packedTile8192 45977856 45994240 11 930 6780 25 _ _ (882183 / 50000) (1764369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell45994240 :
    ThetaLowerSegment 45994240 46010624 (4598781600979 / 100000) (4600436609117 / 100000) := by
  exact
    packedTile8192 45994240 46010624 11 938 6781 25 _ _ (1764401 / 100000) (441101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46010624 :
    ThetaLowerSegment 46010624 46027008 (4600436609117 / 100000) (4602063420031 / 100000) := by
  exact
    packedTile8192 46010624 46027008 11 922 6783 25 _ _ (1764437 / 100000) (44111 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46027008 :
    ThetaLowerSegment 46027008 46043392 (4602063420031 / 100000) (4603683205327 / 100000) := by
  exact
    packedTile8192 46027008 46043392 11 918 6784 25 _ _ (220559 / 12500) (70579 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46043392 :
    ThetaLowerSegment 46043392 46059776 (4603683205327 / 100000) (4605336549323 / 100000) := by
  exact
    packedTile8192 46043392 46059776 11 937 6785 25 _ _ (441127 / 25000) (1764511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46059776 :
    ThetaLowerSegment 46059776 46076160 (4605336549323 / 100000) (4607005807947 / 100000) := by
  exact
    packedTile8192 46059776 46076160 11 946 6786 25 _ _ (55142 / 3125) (1764547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46076160 :
    ThetaLowerSegment 46076160 46092544 (4607005807947 / 100000) (1152155099433 / 25000) := by
  exact
    packedTile8192 46076160 46092544 11 915 6787 25 _ _ (1764579 / 100000) (882291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46092544 :
    ThetaLowerSegment 46092544 46108928 (1152155099433 / 25000) (4610235020457 / 100000) := by
  exact
    packedTile8192 46092544 46108928 11 915 6789 25 _ _ (352923 / 20000) (882309 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46108928 :
    ThetaLowerSegment 46108928 46125312 (4610235020457 / 100000) (4611863792407 / 100000) := by
  exact
    packedTile8192 46108928 46125312 11 923 6790 25 _ _ (35293 / 2000) (1764653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46125312 :
    ThetaLowerSegment 46125312 46141696 (4611863792407 / 100000) (4613473186039 / 100000) := by
  exact
    packedTile8192 46125312 46141696 11 912 6791 25 _ _ (882343 / 50000) (1764689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46141696 :
    ThetaLowerSegment 46141696 46158080 (4613473186039 / 100000) (2307547482319 / 50000) := by
  exact
    packedTile8192 46141696 46158080 11 919 6792 25 _ _ (1764721 / 100000) (441181 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46158080 :
    ThetaLowerSegment 46158080 46174464 (2307547482319 / 50000) (288546894169 / 6250) := by
  exact
    packedTile8192 46158080 46174464 11 938 6793 25 _ _ (1764757 / 100000) (44119 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46174464 :
    ThetaLowerSegment 46174464 46190848 (288546894169 / 6250) (577296077621 / 12500) := by
  exact
    packedTile8192 46174464 46190848 11 917 6795 25 _ _ (220599 / 12500) (352959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46190848 :
    ThetaLowerSegment 46190848 46207232 (577296077621 / 12500) (577510504223 / 12500) := by
  exact
    packedTile8192 46190848 46207232 11 972 6796 25 _ _ (441207 / 25000) (1764831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46207232 :
    ThetaLowerSegment 46207232 46223616 (577510504223 / 12500) (4621691823977 / 100000) := by
  exact
    packedTile8192 46207232 46223616 11 911 6797 25 _ _ (1764863 / 100000) (882433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46223616 :
    ThetaLowerSegment 46223616 46240000 (4621691823977 / 100000) (1155829323989 / 25000) := by
  exact
    packedTile8192 46223616 46240000 11 921 6798 25 _ _ (1764899 / 100000) (882451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46240000 :
    ThetaLowerSegment 46240000 46256384 (1155829323989 / 25000) (2312473165019 / 50000) := by
  exact
    packedTile8192 46240000 46256384 11 923 6800 25 _ _ (882467 / 50000) (1764937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46256384 :
    ThetaLowerSegment 46256384 46272768 (2312473165019 / 50000) (1156645614307 / 25000) := by
  exact
    packedTile8192 46256384 46272768 11 927 6801 25 _ _ (176497 / 10000) (1764973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46272768 :
    ThetaLowerSegment 46272768 46289152 (1156645614307 / 25000) (4628151546673 / 100000) := by
  exact
    packedTile8192 46272768 46289152 11 889 6802 25 _ _ (353001 / 20000) (110313 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46289152 :
    ThetaLowerSegment 46289152 46305536 (4628151546673 / 100000) (4629789503793 / 100000) := by
  exact
    packedTile8192 46289152 46305536 11 928 6803 25 _ _ (22063 / 1250) (1765043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46305536 :
    ThetaLowerSegment 46305536 46321920 (4629789503793 / 100000) (4631429259397 / 100000) := by
  exact
    packedTile8192 46305536 46321920 11 929 6804 25 _ _ (441269 / 25000) (1765079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46321920 :
    ThetaLowerSegment 46321920 46338304 (4631429259397 / 100000) (231655570509 / 5000) := by
  exact
    packedTile8192 46321920 46338304 11 953 6806 25 _ _ (1765111 / 100000) (882557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46338304 :
    ThetaLowerSegment 46338304 46354688 (231655570509 / 5000) (2317375615407 / 50000) := by
  exact
    packedTile8192 46338304 46354688 11 929 6807 25 _ _ (882573 / 50000) (1765149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46354688 :
    ThetaLowerSegment 46354688 46371072 (2317375615407 / 50000) (579544031361 / 12500) := by
  exact
    packedTile8192 46354688 46371072 11 907 6808 25 _ _ (882591 / 50000) (353037 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46371072 :
    ThetaLowerSegment 46371072 46387456 (579544031361 / 12500) (2319002247 / 50) := by
  exact
    packedTile8192 46371072 46387456 11 936 6809 25 _ _ (1765217 / 100000) (88261 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46387456 :
    ThetaLowerSegment 46387456 46403840 (2319002247 / 50) (1159910220651 / 25000) := by
  exact
    packedTile8192 46387456 46403840 11 927 6810 25 _ _ (441313 / 25000) (353051 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46403840 :
    ThetaLowerSegment 46403840 46420224 (1159910220651 / 25000) (1160325063331 / 25000) := by
  exact
    packedTile8192 46403840 46420224 11 940 6812 25 _ _ (220661 / 12500) (1765291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46420224 :
    ThetaLowerSegment 46420224 46436608 (1160325063331 / 25000) (928583810903 / 20000) := by
  exact
    packedTile8192 46420224 46436608 11 917 6813 25 _ _ (1765323 / 100000) (882663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46436608 :
    ThetaLowerSegment 46436608 46452992 (928583810903 / 20000) (4644513172789 / 100000) := by
  exact
    packedTile8192 46436608 46452992 11 903 6814 25 _ _ (882679 / 50000) (1765361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46452992 :
    ThetaLowerSegment 46452992 46469376 (4644513172789 / 100000) (4646139100663 / 100000) := by
  exact
    packedTile8192 46452992 46469376 11 921 6815 25 _ _ (882697 / 50000) (1765397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46469376 :
    ThetaLowerSegment 46469376 46485760 (4646139100663 / 100000) (4647826850787 / 100000) := by
  exact
    packedTile8192 46469376 46485760 11 956 6816 25 _ _ (1765429 / 100000) (220679 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46485760 :
    ThetaLowerSegment 46485760 46502144 (4647826850787 / 100000) (4649465201379 / 100000) := by
  exact
    packedTile8192 46485760 46502144 11 928 6818 25 _ _ (220683 / 12500) (1765467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46502144 :
    ThetaLowerSegment 46502144 46518528 (4649465201379 / 100000) (4651156549421 / 100000) := by
  exact
    packedTile8192 46502144 46518528 11 958 6819 25 _ _ (1765499 / 100000) (882751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46518528 :
    ThetaLowerSegment 46518528 46534912 (4651156549421 / 100000) (2326386006973 / 50000) := by
  exact
    packedTile8192 46518528 46534912 11 915 6820 25 _ _ (353107 / 20000) (882769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46534912 :
    ThetaLowerSegment 46534912 46551296 (2326386006973 / 50000) (1163599525979 / 25000) := by
  exact
    packedTile8192 46534912 46551296 11 921 6821 25 _ _ (176557 / 10000) (1765573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46551296 :
    ThetaLowerSegment 46551296 46567680 (1163599525979 / 25000) (582003690367 / 12500) := by
  exact
    packedTile8192 46551296 46567680 11 924 6822 25 _ _ (353121 / 20000) (220701 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46567680 :
    ThetaLowerSegment 46567680 46584064 (582003690367 / 12500) (291103700541 / 6250) := by
  exact
    packedTile8192 46567680 46584064 11 923 6824 25 _ _ (44141 / 2500) (1765643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46584064 :
    ThetaLowerSegment 46584064 46600448 (291103700541 / 6250) (582410453707 / 12500) := by
  exact
    packedTile8192 46584064 46600448 11 920 6825 25 _ _ (70627 / 4000) (882839 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46600448 :
    ThetaLowerSegment 46600448 46616832 (582410453707 / 12500) (93219362359 / 2000) := by
  exact
    packedTile8192 46600448 46616832 11 954 6826 25 _ _ (1765711 / 100000) (882857 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46616832 :
    ThetaLowerSegment 46616832 46633216 (93219362359 / 2000) (2331315725341 / 50000) := by
  exact
    packedTile8192 46616832 46633216 11 942 6827 25 _ _ (882873 / 50000) (1765749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46633216 :
    ThetaLowerSegment 46633216 46649600 (2331315725341 / 50000) (932855784871 / 20000) := by
  exact
    packedTile8192 46633216 46649600 11 933 6828 25 _ _ (1765781 / 100000) (220723 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46649600 :
    ThetaLowerSegment 46649600 46665984 (932855784871 / 20000) (4665919367419 / 100000) := by
  exact
    packedTile8192 46649600 46665984 11 929 6830 25 _ _ (220727 / 12500) (1765819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46665984 :
    ThetaLowerSegment 46665984 46682368 (4665919367419 / 100000) (46675633747 / 1000) := by
  exact
    packedTile8192 46665984 46682368 11 931 6831 25 _ _ (1765851 / 100000) (882927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46682368 :
    ThetaLowerSegment 46682368 46698752 (46675633747 / 1000) (2334610770827 / 50000) := by
  exact
    packedTile8192 46682368 46698752 11 939 6832 25 _ _ (882943 / 50000) (1765889 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46698752 :
    ThetaLowerSegment 46698752 46715136 (2334610770827 / 50000) (4670844423053 / 100000) := by
  exact
    packedTile8192 46698752 46715136 11 919 6833 25 _ _ (1765921 / 100000) (441481 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46715136 :
    ThetaLowerSegment 46715136 46731520 (4670844423053 / 100000) (4672449677057 / 100000) := by
  exact
    packedTile8192 46715136 46731520 11 909 6834 25 _ _ (441489 / 25000) (1765959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46731520 :
    ThetaLowerSegment 46731520 46747904 (4672449677057 / 100000) (4674081452741 / 100000) := by
  exact
    packedTile8192 46731520 46747904 11 924 6836 25 _ _ (1765991 / 100000) (882997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46747904 :
    ThetaLowerSegment 46747904 46764288 (4674081452741 / 100000) (4675734453077 / 100000) := by
  exact
    packedTile8192 46747904 46764288 11 936 6837 25 _ _ (883013 / 50000) (1766029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46764288 :
    ThetaLowerSegment 46764288 46780672 (4675734453077 / 100000) (4677412211977 / 100000) := by
  exact
    packedTile8192 46764288 46780672 11 950 6838 25 _ _ (883031 / 50000) (353213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46780672 :
    ThetaLowerSegment 46780672 46797056 (4677412211977 / 100000) (584877640793 / 12500) := by
  exact
    packedTile8192 46780672 46797056 11 911 6839 25 _ _ (1766097 / 100000) (17661 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46797056 :
    ThetaLowerSegment 46797056 46813440 (584877640793 / 12500) (1170169881073 / 25000) := by
  exact
    packedTile8192 46797056 46813440 11 939 6840 25 _ _ (441533 / 25000) (353227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46813440 :
    ThetaLowerSegment 46813440 46829824 (1170169881073 / 25000) (1170583164151 / 25000) := by
  exact
    packedTile8192 46813440 46829824 11 936 6842 25 _ _ (1766167 / 100000) (176617 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46829824 :
    ThetaLowerSegment 46829824 46846208 (1170583164151 / 25000) (1170985858207 / 25000) := by
  exact
    packedTile8192 46829824 46846208 11 912 6843 25 _ _ (883101 / 50000) (353241 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46846208 :
    ThetaLowerSegment 46846208 46862592 (1170985858207 / 25000) (2342778886723 / 50000) := by
  exact
    packedTile8192 46846208 46862592 11 914 6844 25 _ _ (1766237 / 100000) (11039 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46862592 :
    ThetaLowerSegment 46862592 46878976 (2342778886723 / 50000) (2343613450243 / 50000) := by
  exact
    packedTile8192 46862592 46878976 11 945 6845 25 _ _ (55196 / 3125) (70651 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46878976 :
    ThetaLowerSegment 46878976 46895360 (2343613450243 / 50000) (1172219599149 / 25000) := by
  exact
    packedTile8192 46878976 46895360 11 935 6846 25 _ _ (883153 / 50000) (1766309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46895360 :
    ThetaLowerSegment 46895360 46911744 (1172219599149 / 25000) (4690544056159 / 100000) := by
  exact
    packedTile8192 46895360 46911744 11 943 6848 25 _ _ (1766341 / 100000) (220793 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46911744 :
    ThetaLowerSegment 46911744 46928128 (4690544056159 / 100000) (4692139093687 / 100000) := by
  exact
    packedTile8192 46911744 46928128 11 903 6849 25 _ _ (220797 / 12500) (1766379 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46928128 :
    ThetaLowerSegment 46928128 46944512 (4692139093687 / 100000) (4693810118493 / 100000) := by
  exact
    packedTile8192 46928128 46944512 11 946 6850 25 _ _ (1766411 / 100000) (883207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46944512 :
    ThetaLowerSegment 46944512 46960896 (4693810118493 / 100000) (4695422883691 / 100000) := by
  exact
    packedTile8192 46944512 46960896 11 913 6851 25 _ _ (883223 / 50000) (1766449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46960896 :
    ThetaLowerSegment 46960896 46977280 (4695422883691 / 100000) (939411022427 / 20000) := by
  exact
    packedTile8192 46960896 46977280 11 924 6852 25 _ _ (1766481 / 100000) (441621 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46977280 :
    ThetaLowerSegment 46977280 46993664 (939411022427 / 20000) (4698683839887 / 100000) := by
  exact
    packedTile8192 46977280 46993664 11 922 6853 25 _ _ (441629 / 25000) (1766519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell46993664 :
    ThetaLowerSegment 46993664 47010048 (4698683839887 / 100000) (2350176615291 / 50000) := by
  exact
    packedTile8192 46993664 47010048 11 945 6855 25 _ _ (1766551 / 100000) (883277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47010048 :
    ThetaLowerSegment 47010048 47026432 (2350176615291 / 50000) (2350994544609 / 50000) := by
  exact
    packedTile8192 47010048 47026432 11 926 6856 25 _ _ (883293 / 50000) (1766589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47026432 :
    ThetaLowerSegment 47026432 47042816 (2350994544609 / 50000) (293977444577 / 6250) := by
  exact
    packedTile8192 47026432 47042816 11 934 6857 25 _ _ (1766621 / 100000) (55207 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47042816 :
    ThetaLowerSegment 47042816 47059200 (293977444577 / 6250) (4705195536287 / 100000) := by
  exact
    packedTile8192 47042816 47059200 11 881 6858 25 _ _ (353331 / 20000) (883329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47059200 :
    ThetaLowerSegment 47059200 47075584 (4705195536287 / 100000) (4706757290247 / 100000) := by
  exact
    packedTile8192 47059200 47075584 11 884 6859 25 _ _ (176669 / 10000) (1766693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47075584 :
    ThetaLowerSegment 47075584 47091968 (4706757290247 / 100000) (1177106711343 / 25000) := by
  exact
    packedTile8192 47075584 47091968 11 945 6861 25 _ _ (70669 / 4000) (220841 / 12500) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47091968 :
    ThetaLowerSegment 47091968 47108352 (1177106711343 / 25000) (1177520574873 / 25000) := by
  exact
    packedTile8192 47091968 47108352 11 937 6862 25 _ _ (44169 / 2500) (1766763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47108352 :
    ThetaLowerSegment 47108352 47124736 (1177520574873 / 25000) (2355852108651 / 50000) := by
  exact
    packedTile8192 47108352 47124736 11 918 6863 25 _ _ (353359 / 20000) (883399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47124736 :
    ThetaLowerSegment 47124736 47141120 (2355852108651 / 50000) (4713388005339 / 100000) := by
  exact
    packedTile8192 47124736 47141120 11 953 6864 25 _ _ (1766829 / 100000) (110427 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47141120 :
    ThetaLowerSegment 47141120 47157504 (4713388005339 / 100000) (4715052391227 / 100000) := by
  exact
    packedTile8192 47141120 47157504 11 942 6865 25 _ _ (110429 / 6250) (1766867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47157504 :
    ThetaLowerSegment 47157504 47173888 (4715052391227 / 100000) (471667263761 / 10000) := by
  exact
    packedTile8192 47157504 47173888 11 917 6867 25 _ _ (1766899 / 100000) (883451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47173888 :
    ThetaLowerSegment 47173888 47190272 (471667263761 / 10000) (2359163243917 / 50000) := by
  exact
    packedTile8192 47173888 47190272 11 936 6868 25 _ _ (883467 / 50000) (1766937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47190272 :
    ThetaLowerSegment 47190272 47206656 (2359163243917 / 50000) (2360001670233 / 50000) := by
  exact
    packedTile8192 47190272 47206656 11 949 6869 25 _ _ (220871 / 12500) (1766971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47206656 :
    ThetaLowerSegment 47206656 47223040 (2360001670233 / 50000) (4721613080199 / 100000) := by
  exact
    packedTile8192 47206656 47223040 11 911 6870 25 _ _ (1767003 / 100000) (883503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47223040 :
    ThetaLowerSegment 47223040 47239424 (4721613080199 / 100000) (4723221084779 / 100000) := by
  exact
    packedTile8192 47223040 47239424 11 910 6871 25 _ _ (883519 / 50000) (1767041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47239424 :
    ThetaLowerSegment 47239424 47255808 (4723221084779 / 100000) (4724839722731 / 100000) := by
  exact
    packedTile8192 47239424 47255808 11 916 6873 25 _ _ (55221 / 3125) (70683 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47255808 :
    ThetaLowerSegment 47255808 47272192 (4724839722731 / 100000) (236325658653 / 5000) := by
  exact
    packedTile8192 47255808 47272192 11 947 6874 25 _ _ (1767107 / 100000) (176711 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47272192 :
    ThetaLowerSegment 47272192 47288576 (236325658653 / 5000) (1182040037351 / 25000) := by
  exact
    packedTile8192 47272192 47288576 11 932 6875 25 _ _ (883571 / 50000) (353429 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47288576 :
    ThetaLowerSegment 47288576 47304960 (1182040037351 / 25000) (1182452672947 / 25000) := by
  exact
    packedTile8192 47288576 47304960 11 934 6876 25 _ _ (220897 / 12500) (1767179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47304960 :
    ThetaLowerSegment 47304960 47321344 (1182452672947 / 25000) (2365727099009 / 50000) := by
  exact
    packedTile8192 47304960 47321344 11 930 6877 25 _ _ (1767211 / 100000) (883607 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47321344 :
    ThetaLowerSegment 47321344 47337728 (2365727099009 / 50000) (236654621753 / 5000) := by
  exact
    packedTile8192 47321344 47337728 11 927 6879 25 _ _ (883623 / 50000) (1767249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47337728 :
    ThetaLowerSegment 47337728 47354112 (236654621753 / 5000) (236734767901 / 5000) := by
  exact
    packedTile8192 47337728 47354112 11 907 6880 25 _ _ (22091 / 1250) (1767283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47354112 :
    ThetaLowerSegment 47354112 47370496 (236734767901 / 5000) (236816064391 / 5000) := by
  exact
    packedTile8192 47354112 47370496 11 920 6881 25 _ _ (353463 / 20000) (883659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47370496 :
    ThetaLowerSegment 47370496 47386880 (236816064391 / 5000) (59225003379 / 1250) := by
  exact
    packedTile8192 47370496 47386880 11 950 6882 25 _ _ (35347 / 2000) (1767353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47386880 :
    ThetaLowerSegment 47386880 47403264 (59225003379 / 1250) (296227525167 / 6250) := by
  exact
    packedTile8192 47386880 47403264 11 928 6883 25 _ _ (220923 / 12500) (1767387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47403264 :
    ThetaLowerSegment 47403264 47419648 (296227525167 / 6250) (4741229312353 / 100000) := by
  exact
    packedTile8192 47403264 47419648 11 899 6885 25 _ _ (1767419 / 100000) (883711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47419648 :
    ThetaLowerSegment 47419648 47436032 (4741229312353 / 100000) (189714497557 / 4000) := by
  exact
    packedTile8192 47419648 47436032 11 924 6886 25 _ _ (1767453 / 100000) (55233 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47436032 :
    ThetaLowerSegment 47436032 47452416 (189714497557 / 4000) (948895938089 / 20000) := by
  exact
    packedTile8192 47436032 47452416 11 915 6887 25 _ _ (55234 / 3125) (1767491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47452416 :
    ThetaLowerSegment 47452416 47468800 (948895938089 / 20000) (4746095205553 / 100000) := by
  exact
    packedTile8192 47452416 47468800 11 914 6888 25 _ _ (883761 / 50000) (70701 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47468800 :
    ThetaLowerSegment 47468800 47485184 (4746095205553 / 100000) (296735567627 / 6250) := by
  exact
    packedTile8192 47468800 47485184 11 947 6889 26 _ _ (1767557 / 100000) (44189 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47485184 :
    ThetaLowerSegment 47485184 47501568 (296735567627 / 6250) (4749474807347 / 100000) := by
  exact
    packedTile8192 47485184 47501568 11 965 6890 26 _ _ (1767591 / 100000) (883797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47501568 :
    ThetaLowerSegment 47501568 47517952 (4749474807347 / 100000) (4751083347007 / 100000) := by
  exact
    packedTile8192 47501568 47517952 11 910 6892 26 _ _ (883813 / 50000) (1767629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47517952 :
    ThetaLowerSegment 47517952 47534336 (4751083347007 / 100000) (4752760856347 / 100000) := by
  exact
    packedTile8192 47517952 47534336 11 949 6893 26 _ _ (88383 / 5000) (1767663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47534336 :
    ThetaLowerSegment 47534336 47550720 (4752760856347 / 100000) (4754365923407 / 100000) := by
  exact
    packedTile8192 47534336 47550720 11 908 6894 26 _ _ (353539 / 20000) (883849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47550720 :
    ThetaLowerSegment 47550720 47567104 (4754365923407 / 100000) (1189003803641 / 25000) := by
  exact
    packedTile8192 47550720 47567104 11 933 6895 26 _ _ (1767729 / 100000) (441933 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47567104 :
    ThetaLowerSegment 47567104 47583488 (1189003803641 / 25000) (118940552801 / 2500) := by
  exact
    packedTile8192 47567104 47583488 11 909 6896 26 _ _ (441941 / 25000) (1767767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47583488 :
    ThetaLowerSegment 47583488 47599872 (118940552801 / 2500) (475925732519 / 10000) := by
  exact
    packedTile8192 47583488 47599872 11 925 6898 26 _ _ (883899 / 50000) (1767801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47599872 :
    ThetaLowerSegment 47599872 47616256 (475925732519 / 10000) (2380452472773 / 50000) := by
  exact
    packedTile8192 47599872 47616256 11 932 6899 26 _ _ (1767833 / 100000) (441959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47616256 :
    ThetaLowerSegment 47616256 47632640 (2380452472773 / 50000) (2381262155859 / 50000) := by
  exact
    packedTile8192 47616256 47632640 11 916 6900 26 _ _ (1767867 / 100000) (176787 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47632640 :
    ThetaLowerSegment 47632640 47649024 (2381262155859 / 50000) (4764134869529 / 100000) := by
  exact
    packedTile8192 47632640 47649024 11 911 6901 26 _ _ (1767901 / 100000) (55247 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47649024 :
    ThetaLowerSegment 47649024 47665408 (4764134869529 / 100000) (953143788037 / 20000) := by
  exact
    packedTile8192 47649024 47665408 11 896 6902 26 _ _ (55248 / 3125) (1767939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47665408 :
    ThetaLowerSegment 47665408 47681792 (953143788037 / 20000) (953469094517 / 20000) := by
  exact
    packedTile8192 47665408 47681792 11 920 6904 26 _ _ (176797 / 10000) (1767973 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47681792 :
    ThetaLowerSegment 47681792 47698176 (953469094517 / 20000) (953803601063 / 20000) := by
  exact
    packedTile8192 47681792 47698176 11 946 6905 26 _ _ (353601 / 20000) (221001 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47698176 :
    ThetaLowerSegment 47698176 47714560 (953803601063 / 20000) (954121848083 / 20000) := by
  exact
    packedTile8192 47698176 47714560 11 900 6906 26 _ _ (1768039 / 100000) (884021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47714560 :
    ThetaLowerSegment 47714560 47730944 (954121848083 / 20000) (4772292445911 / 100000) := by
  exact
    packedTile8192 47714560 47730944 11 952 6907 26 _ _ (1768073 / 100000) (442019 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47730944 :
    ThetaLowerSegment 47730944 47747328 (4772292445911 / 100000) (954776041379 / 20000) := by
  exact
    packedTile8192 47730944 47747328 11 898 6908 26 _ _ (442027 / 25000) (1768111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47747328 :
    ThetaLowerSegment 47747328 47763712 (954776041379 / 20000) (4775510433819 / 100000) := by
  exact
    packedTile8192 47747328 47763712 11 922 6909 26 _ _ (884071 / 50000) (353629 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47763712 :
    ThetaLowerSegment 47763712 47780096 (4775510433819 / 100000) (955438393839 / 20000) := by
  exact
    packedTile8192 47763712 47780096 11 951 6911 26 _ _ (110511 / 6250) (1768179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47780096 :
    ThetaLowerSegment 47780096 47796480 (955438393839 / 20000) (38230380031 / 800) := by
  exact
    packedTile8192 47780096 47796480 11 908 6912 26 _ _ (176821 / 10000) (1768213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47796480 :
    ThetaLowerSegment 47796480 47812864 (38230380031 / 800) (239022363823 / 5000) := by
  exact
    packedTile8192 47796480 47812864 11 933 6913 26 _ _ (353649 / 20000) (221031 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47812864 :
    ThetaLowerSegment 47812864 47829248 (239022363823 / 5000) (4782104153883 / 100000) := by
  exact
    packedTile8192 47812864 47829248 11 937 6914 26 _ _ (1768279 / 100000) (884141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47829248 :
    ThetaLowerSegment 47829248 47845632 (4782104153883 / 100000) (1195933192539 / 25000) := by
  exact
    packedTile8192 47829248 47845632 11 921 6915 26 _ _ (1768313 / 100000) (442079 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47845632 :
    ThetaLowerSegment 47845632 47862016 (1195933192539 / 25000) (598176366551 / 12500) := by
  exact
    packedTile8192 47845632 47862016 11 949 6917 26 _ _ (442087 / 25000) (1768351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47862016 :
    ThetaLowerSegment 47862016 47878400 (598176366551 / 12500) (478711034751 / 10000) := by
  exact
    packedTile8192 47862016 47878400 11 961 6918 26 _ _ (884191 / 50000) (353677 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47878400 :
    ThetaLowerSegment 47878400 47894784 (478711034751 / 10000) (2394369529323 / 50000) := by
  exact
    packedTile8192 47878400 47894784 11 921 6919 26 _ _ (55263 / 3125) (1768419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47894784 :
    ThetaLowerSegment 47894784 47911168 (2394369529323 / 50000) (2395181247873 / 50000) := by
  exact
    packedTile8192 47894784 47911168 11 918 6920 26 _ _ (35369 / 2000) (1768453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47911168 :
    ThetaLowerSegment 47911168 47927552 (2395181247873 / 50000) (2395977065673 / 50000) := by
  exact
    packedTile8192 47911168 47927552 11 900 6921 26 _ _ (442121 / 25000) (1768487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47927552 :
    ThetaLowerSegment 47927552 47943936 (2395977065673 / 50000) (4793575863269 / 100000) := by
  exact
    packedTile8192 47927552 47943936 11 917 6922 26 _ _ (1768519 / 100000) (884261 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47943936 :
    ThetaLowerSegment 47943936 47960320 (4793575863269 / 100000) (4795213543347 / 100000) := by
  exact
    packedTile8192 47943936 47960320 11 926 6924 26 _ _ (1768553 / 100000) (442139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47960320 :
    ThetaLowerSegment 47960320 47976704 (4795213543347 / 100000) (4796844180561 / 100000) := by
  exact
    packedTile8192 47960320 47976704 11 922 6925 26 _ _ (1768587 / 100000) (176859 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47976704 :
    ThetaLowerSegment 47976704 47993088 (4796844180561 / 100000) (2399215316799 / 50000) := by
  exact
    packedTile8192 47976704 47993088 11 897 6926 26 _ _ (1768621 / 100000) (110539 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell47993088 :
    ThetaLowerSegment 47993088 48009472 (2399215316799 / 50000) (2400032435409 / 50000) := by
  exact
    packedTile8192 47993088 48009472 11 924 6927 26 _ _ (353731 / 20000) (884329 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48009472 :
    ThetaLowerSegment 48009472 48025856 (2400032435409 / 50000) (4801725669789 / 100000) := by
  exact
    packedTile8192 48009472 48025856 11 939 6928 26 _ _ (1768689 / 100000) (442173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48025856 :
    ThetaLowerSegment 48025856 48042240 (4801725669789 / 100000) (4803354664593 / 100000) := by
  exact
    packedTile8192 48025856 48042240 11 921 6930 26 _ _ (442181 / 25000) (1768727 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48042240 :
    ThetaLowerSegment 48042240 48058624 (4803354664593 / 100000) (960987186849 / 20000) := by
  exact
    packedTile8192 48042240 48058624 11 894 6931 26 _ _ (884379 / 50000) (1768761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48058624 :
    ThetaLowerSegment 48058624 48075008 (960987186849 / 20000) (4806531384629 / 100000) := by
  exact
    packedTile8192 48058624 48075008 11 902 6932 26 _ _ (221099 / 12500) (353759 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48075008 :
    ThetaLowerSegment 48075008 48091392 (4806531384629 / 100000) (961639169979 / 20000) := by
  exact
    packedTile8192 48075008 48091392 11 941 6933 26 _ _ (884413 / 50000) (1768829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48091392 :
    ThetaLowerSegment 48091392 48107776 (961639169979 / 20000) (961973838291 / 20000) := by
  exact
    packedTile8192 48091392 48107776 11 946 6934 26 _ _ (88443 / 5000) (1768863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48107776 :
    ThetaLowerSegment 48107776 48124160 (961973838291 / 20000) (4811512493981 / 100000) := by
  exact
    packedTile8192 48107776 48124160 11 929 6935 26 _ _ (884447 / 50000) (1768897 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48124160 :
    ThetaLowerSegment 48124160 48140544 (4811512493981 / 100000) (192525808581 / 4000) := by
  exact
    packedTile8192 48124160 48140544 11 923 6937 26 _ _ (55279 / 3125) (1768931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48140544 :
    ThetaLowerSegment 48140544 48156928 (192525808581 / 4000) (4814762045793 / 100000) := by
  exact
    packedTile8192 48140544 48156928 11 914 6938 26 _ _ (884481 / 50000) (353793 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48156928 :
    ThetaLowerSegment 48156928 48173312 (4814762045793 / 100000) (4816398367093 / 100000) := by
  exact
    packedTile8192 48156928 48173312 11 925 6939 26 _ _ (442249 / 25000) (1768999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48173312 :
    ThetaLowerSegment 48173312 48189696 (4816398367093 / 100000) (4818015260513 / 100000) := by
  exact
    packedTile8192 48173312 48189696 11 914 6940 26 _ _ (176903 / 10000) (1769033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48189696 :
    ThetaLowerSegment 48189696 48206080 (4818015260513 / 100000) (4819681718801 / 100000) := by
  exact
    packedTile8192 48189696 48206080 11 942 6941 26 _ _ (221133 / 12500) (1769067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48206080 :
    ThetaLowerSegment 48206080 48222464 (4819681718801 / 100000) (4821272137903 / 100000) := by
  exact
    packedTile8192 48206080 48222464 11 899 6943 26 _ _ (884549 / 50000) (1769101 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48222464 :
    ThetaLowerSegment 48222464 48238848 (4821272137903 / 100000) (4822855511043 / 100000) := by
  exact
    packedTile8192 48222464 48238848 11 895 6944 26 _ _ (442283 / 25000) (353827 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48238848 :
    ThetaLowerSegment 48238848 48255232 (4822855511043 / 100000) (4824497297091 / 100000) := by
  exact
    packedTile8192 48238848 48255232 11 928 6945 26 _ _ (884583 / 50000) (1769169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48255232 :
    ThetaLowerSegment 48255232 48271616 (4824497297091 / 100000) (4826183344691 / 100000) := by
  exact
    packedTile8192 48255232 48271616 11 953 6946 26 _ _ (4423 / 250) (1769203 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48271616 :
    ThetaLowerSegment 48271616 48288000 (4826183344691 / 100000) (4827819886141 / 100000) := by
  exact
    packedTile8192 48271616 48288000 11 925 6947 26 _ _ (884617 / 50000) (1769237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48288000 :
    ThetaLowerSegment 48288000 48304384 (4827819886141 / 100000) (4829458228309 / 100000) := by
  exact
    packedTile8192 48288000 48304384 11 926 6948 26 _ _ (442317 / 25000) (1769271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48304384 :
    ThetaLowerSegment 48304384 48320768 (4829458228309 / 100000) (4831133757303 / 100000) := by
  exact
    packedTile8192 48304384 48320768 11 947 6950 26 _ _ (884651 / 50000) (353861 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48320768 :
    ThetaLowerSegment 48320768 48337152 (4831133757303 / 100000) (4832758007751 / 100000) := by
  exact
    packedTile8192 48320768 48337152 11 918 6951 26 _ _ (221167 / 12500) (1769339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48337152 :
    ThetaLowerSegment 48337152 48353536 (4832758007751 / 100000) (4834424754291 / 100000) := by
  exact
    packedTile8192 48337152 48353536 11 942 6952 26 _ _ (176937 / 10000) (1769373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48353536 :
    ThetaLowerSegment 48353536 48369920 (4834424754291 / 100000) (483600483117 / 10000) := by
  exact
    packedTile8192 48353536 48369920 11 893 6953 26 _ _ (1769403 / 100000) (884703 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48369920 :
    ThetaLowerSegment 48369920 48386304 (483600483117 / 10000) (2418826973227 / 50000) := by
  exact
    packedTile8192 48369920 48386304 11 932 6954 26 _ _ (1769437 / 100000) (11059 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48386304 :
    ThetaLowerSegment 48386304 48402688 (2418826973227 / 50000) (4839347330201 / 100000) := by
  exact
    packedTile8192 48386304 48402688 11 957 6956 26 _ _ (1769471 / 100000) (884737 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48402688 :
    ThetaLowerSegment 48402688 48419072 (4839347330201 / 100000) (2420477905123 / 50000) := by
  exact
    packedTile8192 48402688 48419072 11 909 6957 26 _ _ (353901 / 20000) (442377 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48419072 :
    ThetaLowerSegment 48419072 48435456 (2420477905123 / 50000) (4842539547651 / 100000) := by
  exact
    packedTile8192 48419072 48435456 11 895 6958 26 _ _ (1769539 / 100000) (884771 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48435456 :
    ThetaLowerSegment 48435456 48451840 (4842539547651 / 100000) (4844160476519 / 100000) := by
  exact
    packedTile8192 48435456 48451840 11 916 6959 26 _ _ (1769573 / 100000) (221197 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48451840 :
    ThetaLowerSegment 48451840 48468224 (4844160476519 / 100000) (2422909299139 / 50000) := by
  exact
    packedTile8192 48451840 48468224 11 937 6960 26 _ _ (1769607 / 100000) (176961 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48468224 :
    ThetaLowerSegment 48468224 48484608 (2422909299139 / 50000) (2423709176419 / 50000) := by
  exact
    packedTile8192 48468224 48484608 11 904 6961 26 _ _ (44241 / 2500) (1769643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48484608 :
    ThetaLowerSegment 48484608 48500992 (2423709176419 / 50000) (2424562159287 / 50000) := by
  exact
    packedTile8192 48484608 48500992 11 964 6963 26 _ _ (884837 / 50000) (1769677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48500992 :
    ThetaLowerSegment 48500992 48517376 (2424562159287 / 50000) (2425392152339 / 50000) := by
  exact
    packedTile8192 48500992 48517376 11 938 6964 26 _ _ (442427 / 25000) (1769711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48517376 :
    ThetaLowerSegment 48517376 48533760 (2425392152339 / 50000) (485244078319 / 10000) := by
  exact
    packedTile8192 48517376 48533760 11 936 6965 26 _ _ (884871 / 50000) (353949 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48533760 :
    ThetaLowerSegment 48533760 48550144 (485244078319 / 10000) (485407782599 / 10000) := by
  exact
    packedTile8192 48533760 48550144 11 925 6966 26 _ _ (110611 / 6250) (1769779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48550144 :
    ThetaLowerSegment 48550144 48566528 (485407782599 / 10000) (2427821168573 / 50000) := by
  exact
    packedTile8192 48550144 48566528 11 884 6967 26 _ _ (1769809 / 100000) (442453 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48566528 :
    ThetaLowerSegment 48566528 48582912 (2427821168573 / 50000) (4857304219723 / 100000) := by
  exact
    packedTile8192 48566528 48582912 11 939 6968 26 _ _ (1769843 / 100000) (884923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48582912 :
    ThetaLowerSegment 48582912 48599296 (4857304219723 / 100000) (2429468908097 / 50000) := by
  exact
    packedTile8192 48582912 48599296 11 923 6970 26 _ _ (1769877 / 100000) (44247 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48599296 :
    ThetaLowerSegment 48599296 48615680 (2429468908097 / 50000) (2430300765797 / 50000) := by
  exact
    packedTile8192 48599296 48615680 11 940 6971 26 _ _ (176991 / 10000) (1769913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48615680 :
    ThetaLowerSegment 48615680 48632064 (2430300765797 / 50000) (2431112285121 / 50000) := by
  exact
    packedTile8192 48615680 48632064 11 917 6972 26 _ _ (221243 / 12500) (1769947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48632064 :
    ThetaLowerSegment 48632064 48648448 (2431112285121 / 50000) (1215947750193 / 25000) := by
  exact
    packedTile8192 48632064 48648448 11 885 6973 26 _ _ (884989 / 50000) (1769981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48648448 :
    ThetaLowerSegment 48648448 48664832 (1215947750193 / 25000) (304093691397 / 6250) := by
  exact
    packedTile8192 48648448 48664832 11 965 6974 26 _ _ (442503 / 25000) (354003 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48664832 :
    ThetaLowerSegment 48664832 48681216 (304093691397 / 6250) (2433558441741 / 50000) := by
  exact
    packedTile8192 48664832 48681216 11 914 6976 26 _ _ (354009 / 20000) (55314 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48681216 :
    ThetaLowerSegment 48681216 48697600 (2433558441741 / 50000) (4868750666399 / 100000) := by
  exact
    packedTile8192 48681216 48697600 11 923 6977 26 _ _ (1770079 / 100000) (885041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48697600 :
    ThetaLowerSegment 48697600 48713984 (4868750666399 / 100000) (608797617559 / 12500) := by
  exact
    packedTile8192 48697600 48713984 11 921 6978 26 _ _ (1770113 / 100000) (442529 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48713984 :
    ThetaLowerSegment 48713984 48730368 (608797617559 / 12500) (2435993231447 / 50000) := by
  exact
    packedTile8192 48713984 48730368 11 907 6979 26 _ _ (885073 / 50000) (1770149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48730368 :
    ThetaLowerSegment 48730368 48746752 (2435993231447 / 50000) (2436797778257 / 50000) := by
  exact
    packedTile8192 48730368 48746752 11 909 6980 26 _ _ (88509 / 5000) (1770183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48746752 :
    ThetaLowerSegment 48746752 48763136 (2436797778257 / 50000) (1218796301947 / 25000) := by
  exact
    packedTile8192 48746752 48763136 11 898 6981 26 _ _ (1770213 / 100000) (221277 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48763136 :
    ThetaLowerSegment 48763136 48779520 (1218796301947 / 25000) (2438405147267 / 50000) := by
  exact
    packedTile8192 48763136 48779520 11 918 6983 26 _ _ (1770247 / 100000) (7081 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48779520 :
    ThetaLowerSegment 48779520 48795904 (2438405147267 / 50000) (2439230098213 / 50000) := by
  exact
    packedTile8192 48779520 48795904 11 932 6984 26 _ _ (1770281 / 100000) (442571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48795904 :
    ThetaLowerSegment 48795904 48812288 (2439230098213 / 50000) (1220036826417 / 25000) := by
  exact
    packedTile8192 48795904 48812288 11 953 6985 26 _ _ (885157 / 50000) (1770317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48812288 :
    ThetaLowerSegment 48812288 48828672 (1220036826417 / 25000) (1220467020981 / 25000) := by
  exact
    packedTile8192 48812288 48828672 11 972 6986 26 _ _ (442587 / 25000) (1770351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48828672 :
    ThetaLowerSegment 48828672 48845056 (1220467020981 / 25000) (48834543453 / 1000) := by
  exact
    packedTile8192 48828672 48845056 11 896 6987 26 _ _ (1770381 / 100000) (110649 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48845056 :
    ThetaLowerSegment 48845056 48861440 (48834543453 / 1000) (488507958627 / 10000) := by
  exact
    packedTile8192 48845056 48861440 11 918 6988 26 _ _ (354083 / 20000) (885209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48861440 :
    ThetaLowerSegment 48861440 48877824 (488507958627 / 10000) (2443369248023 / 50000) := by
  exact
    packedTile8192 48861440 48877824 11 937 6990 26 _ _ (110653 / 6250) (1770451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48877824 :
    ThetaLowerSegment 48877824 48894208 (2443369248023 / 50000) (1222100244661 / 25000) := by
  exact
    packedTile8192 48877824 48894208 11 939 6991 26 _ _ (885241 / 50000) (354097 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48894208 :
    ThetaLowerSegment 48894208 48910592 (1222100244661 / 25000) (4889989130599 / 100000) := by
  exact
    packedTile8192 48894208 48910592 11 897 6992 26 _ _ (354103 / 20000) (885259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48910592 :
    ThetaLowerSegment 48910592 48926976 (4889989130599 / 100000) (4891614494581 / 100000) := by
  exact
    packedTile8192 48910592 48926976 11 918 6993 26 _ _ (1770549 / 100000) (221319 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48926976 :
    ThetaLowerSegment 48926976 48943360 (4891614494581 / 100000) (4893284153407 / 100000) := by
  exact
    packedTile8192 48926976 48943360 11 943 6994 26 _ _ (885291 / 50000) (354117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48943360 :
    ThetaLowerSegment 48943360 48959744 (4893284153407 / 100000) (978987227627 / 20000) := by
  exact
    packedTile8192 48943360 48959744 11 933 6995 26 _ _ (221327 / 12500) (1770619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48959744 :
    ThetaLowerSegment 48959744 48976128 (978987227627 / 20000) (489655628197 / 10000) := by
  exact
    packedTile8192 48959744 48976128 11 915 6997 26 _ _ (1770649 / 100000) (442663 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48976128 :
    ThetaLowerSegment 48976128 48992512 (489655628197 / 10000) (4898201246477 / 100000) := by
  exact
    packedTile8192 48976128 48992512 11 929 6998 26 _ _ (1770683 / 100000) (885343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell48992512 :
    ThetaLowerSegment 48992512 49008896 (4898201246477 / 100000) (4899823222333 / 100000) := by
  exact
    packedTile8192 48992512 49008896 11 916 6999 26 _ _ (442679 / 25000) (1770719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49008896 :
    ThetaLowerSegment 49008896 49025280 (4899823222333 / 100000) (4901434604833 / 100000) := by
  exact
    packedTile8192 49008896 49025280 11 910 7000 26 _ _ (7083 / 400) (1770753 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49025280 :
    ThetaLowerSegment 49025280 49041664 (4901434604833 / 100000) (980610620099 / 20000) := by
  exact
    packedTile8192 49025280 49041664 11 914 7001 26 _ _ (1770783 / 100000) (885393 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49041664 :
    ThetaLowerSegment 49041664 49058048 (980610620099 / 20000) (1226183401457 / 25000) := by
  exact
    packedTile8192 49041664 49058048 11 949 7002 26 _ _ (1770817 / 100000) (88541 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49058048 :
    ThetaLowerSegment 49058048 49074432 (1226183401457 / 25000) (1226588926107 / 25000) := by
  exact
    packedTile8192 49058048 49074432 11 916 7004 26 _ _ (35417 / 2000) (1770853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49074432 :
    ThetaLowerSegment 49074432 49090816 (1226588926107 / 25000) (1226999770963 / 25000) := by
  exact
    packedTile8192 49074432 49090816 11 928 7005 26 _ _ (1770883 / 100000) (885443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49090816 :
    ThetaLowerSegment 49090816 49107200 (1226999770963 / 25000) (2454830101999 / 50000) := by
  exact
    packedTile8192 49090816 49107200 11 938 7006 26 _ _ (1770917 / 100000) (44273 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49107200 :
    ThetaLowerSegment 49107200 49123584 (2454830101999 / 50000) (306955038953 / 6250) := by
  exact
    packedTile8192 49107200 49123584 11 915 7007 26 _ _ (35419 / 2000) (1770953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49123584 :
    ThetaLowerSegment 49123584 49139968 (306955038953 / 6250) (4912893988761 / 100000) := by
  exact
    packedTile8192 49123584 49139968 11 911 7008 26 _ _ (1770983 / 100000) (885493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49139968 :
    ThetaLowerSegment 49139968 49156352 (4912893988761 / 100000) (4914548118639 / 100000) := by
  exact
    packedTile8192 49139968 49156352 11 934 7009 26 _ _ (1771017 / 100000) (88551 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49156352 :
    ThetaLowerSegment 49156352 49172736 (4914548118639 / 100000) (4916166858339 / 100000) := by
  exact
    packedTile8192 49156352 49172736 11 914 7011 26 _ _ (35421 / 2000) (1771053 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49172736 :
    ThetaLowerSegment 49172736 49189120 (4916166858339 / 100000) (2458909639389 / 50000) := by
  exact
    packedTile8192 49172736 49189120 11 933 7012 26 _ _ (1771083 / 100000) (885543 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49189120 :
    ThetaLowerSegment 49189120 49205504 (2458909639389 / 50000) (2459766860017 / 50000) := by
  exact
    packedTile8192 49189120 49205504 11 968 7013 26 _ _ (1771117 / 100000) (22139 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49205504 :
    ThetaLowerSegment 49205504 49221888 (2459766860017 / 50000) (1230293894021 / 25000) := by
  exact
    packedTile8192 49205504 49221888 11 927 7014 26 _ _ (35423 / 2000) (1771153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49221888 :
    ThetaLowerSegment 49221888 49238272 (1230293894021 / 25000) (2461418472869 / 50000) := by
  exact
    packedTile8192 49221888 49238272 11 938 7015 26 _ _ (1771183 / 100000) (885593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49238272 :
    ThetaLowerSegment 49238272 49254656 (2461418472869 / 50000) (2462226147821 / 50000) := by
  exact
    packedTile8192 49238272 49254656 11 912 7016 26 _ _ (1771217 / 100000) (88561 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49254656 :
    ThetaLowerSegment 49254656 49271040 (2462226147821 / 50000) (307879561837 / 6250) := by
  exact
    packedTile8192 49254656 49271040 11 915 7018 26 _ _ (1417 / 80) (1771253 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49271040 :
    ThetaLowerSegment 49271040 49287424 (307879561837 / 6250) (985540868207 / 20000) := by
  exact
    packedTile8192 49271040 49287424 11 921 7019 26 _ _ (1771283 / 100000) (885643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49287424 :
    ThetaLowerSegment 49287424 49303808 (985540868207 / 20000) (4929312695963 / 100000) := by
  exact
    packedTile8192 49287424 49303808 11 908 7020 26 _ _ (442829 / 25000) (1771319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49303808 :
    ThetaLowerSegment 49303808 49320192 (4929312695963 / 100000) (4930940566613 / 100000) := by
  exact
    packedTile8192 49303808 49320192 11 919 7021 26 _ _ (35427 / 2000) (1771353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49320192 :
    ThetaLowerSegment 49320192 49336576 (4930940566613 / 100000) (154143982438 / 3125) := by
  exact
    packedTile8192 49320192 49336576 11 941 7022 26 _ _ (1771383 / 100000) (885693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49336576 :
    ThetaLowerSegment 49336576 49352960 (154143982438 / 3125) (154195796356 / 3125) := by
  exact
    packedTile8192 49336576 49352960 11 936 7024 26 _ _ (221427 / 12500) (1771419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49352960 :
    ThetaLowerSegment 49352960 49369344 (154195796356 / 3125) (4935932416901 / 100000) := by
  exact
    packedTile8192 49352960 49369344 11 941 7025 26 _ _ (1771449 / 100000) (442863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49369344 :
    ThetaLowerSegment 49369344 49385728 (4935932416901 / 100000) (2468787290821 / 50000) := by
  exact
    packedTile8192 49369344 49385728 11 927 7026 26 _ _ (1771483 / 100000) (885743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49385728 :
    ThetaLowerSegment 49385728 49402112 (2468787290821 / 50000) (2469626103647 / 50000) := by
  exact
    packedTile8192 49385728 49402112 11 947 7027 26 _ _ (442879 / 25000) (1771519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49402112 :
    ThetaLowerSegment 49402112 49418496 (2469626103647 / 50000) (123521785077 / 2500) := by
  exact
    packedTile8192 49402112 49418496 11 914 7028 26 _ _ (1771549 / 100000) (55361 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49418496 :
    ThetaLowerSegment 49418496 49434880 (123521785077 / 2500) (617814428897 / 12500) := by
  exact
    packedTile8192 49418496 49434880 11 928 7029 26 _ _ (885791 / 50000) (354317 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49434880 :
    ThetaLowerSegment 49434880 49451264 (617814428897 / 12500) (2472081516563 / 50000) := by
  exact
    packedTile8192 49434880 49451264 11 930 7030 26 _ _ (354323 / 20000) (885809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49451264 :
    ThetaLowerSegment 49451264 49467648 (2472081516563 / 50000) (2472895588819 / 50000) := by
  exact
    packedTile8192 49451264 49467648 11 919 7032 26 _ _ (55364 / 3125) (1771651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49467648 :
    ThetaLowerSegment 49467648 49484032 (2472895588819 / 50000) (2473735365613 / 50000) := by
  exact
    packedTile8192 49467648 49484032 11 948 7033 26 _ _ (1771681 / 100000) (442921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49484032 :
    ThetaLowerSegment 49484032 49500416 (2473735365613 / 50000) (4949152088761 / 100000) := by
  exact
    packedTile8192 49484032 49500416 11 949 7034 26 _ _ (354343 / 20000) (885859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49500416 :
    ThetaLowerSegment 49500416 49516800 (4949152088761 / 100000) (4950794499157 / 100000) := by
  exact
    packedTile8192 49500416 49516800 11 927 7035 26 _ _ (442937 / 25000) (1771751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49516800 :
    ThetaLowerSegment 49516800 49533184 (4950794499157 / 100000) (4952431624801 / 100000) := by
  exact
    packedTile8192 49516800 49533184 11 924 7036 26 _ _ (1771781 / 100000) (221473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49533184 :
    ThetaLowerSegment 49533184 49549568 (4952431624801 / 100000) (4954047519169 / 100000) := by
  exact
    packedTile8192 49533184 49549568 11 912 7037 26 _ _ (885907 / 50000) (1771817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49549568 :
    ThetaLowerSegment 49549568 49565952 (4954047519169 / 100000) (495571837089 / 10000) := by
  exact
    packedTile8192 49549568 49565952 11 943 7039 26 _ _ (1771847 / 100000) (35437 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49565952 :
    ThetaLowerSegment 49565952 49582336 (495571837089 / 10000) (99147749637 / 2000) := by
  exact
    packedTile8192 49565952 49582336 11 942 7040 26 _ _ (44297 / 2500) (1771883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49582336 :
    ThetaLowerSegment 49582336 49598720 (99147749637 / 2000) (6198838499 / 125) := by
  exact
    packedTile8192 49582336 49598720 11 950 7041 26 _ _ (1771913 / 100000) (442979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49598720 :
    ThetaLowerSegment 49598720 49615104 (6198838499 / 125) (1240177905299 / 25000) := by
  exact
    packedTile8192 49598720 49615104 11 926 7042 26 _ _ (885973 / 50000) (1771949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49615104 :
    ThetaLowerSegment 49615104 49631488 (1240177905299 / 25000) (2481179780833 / 50000) := by
  exact
    packedTile8192 49615104 49631488 11 930 7043 26 _ _ (1771979 / 100000) (885991 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49631488 :
    ThetaLowerSegment 49631488 49647872 (2481179780833 / 50000) (2481971870197 / 50000) := by
  exact
    packedTile8192 49631488 49647872 11 894 7044 26 _ _ (443003 / 25000) (354403 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49647872 :
    ThetaLowerSegment 49647872 49664256 (2481971870197 / 50000) (4965611234739 / 100000) := by
  exact
    packedTile8192 49647872 49664256 11 941 7046 26 _ _ (354409 / 20000) (110753 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49664256 :
    ThetaLowerSegment 49664256 49680640 (4965611234739 / 100000) (993447246053 / 20000) := by
  exact
    packedTile8192 49664256 49680640 11 917 7047 26 _ _ (886039 / 50000) (1772081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49680640 :
    ThetaLowerSegment 49680640 49697024 (993447246053 / 20000) (4968873660829 / 100000) := by
  exact
    packedTile8192 49680640 49697024 11 924 7048 26 _ _ (1772111 / 100000) (886057 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49697024 :
    ThetaLowerSegment 49697024 49713408 (4968873660829 / 100000) (4970463273997 / 100000) := by
  exact
    packedTile8192 49697024 49713408 11 897 7049 26 _ _ (110759 / 6250) (1772147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49713408 :
    ThetaLowerSegment 49713408 49729792 (4970463273997 / 100000) (4972111398607 / 100000) := by
  exact
    packedTile8192 49713408 49729792 11 930 7050 26 _ _ (1772177 / 100000) (88609 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49729792 :
    ThetaLowerSegment 49729792 49746176 (4972111398607 / 100000) (4973764870537 / 100000) := by
  exact
    packedTile8192 49729792 49746176 11 933 7051 26 _ _ (177221 / 10000) (1772213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49746176 :
    ThetaLowerSegment 49746176 49762560 (4973764870537 / 100000) (995084737997 / 20000) := by
  exact
    packedTile8192 49746176 49762560 11 936 7053 26 _ _ (1772243 / 100000) (886123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49762560 :
    ThetaLowerSegment 49762560 49778944 (995084737997 / 20000) (4977048867077 / 100000) := by
  exact
    packedTile8192 49762560 49778944 11 917 7054 26 _ _ (443069 / 25000) (1772279 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49778944 :
    ThetaLowerSegment 49778944 49795328 (4977048867077 / 100000) (2489358304923 / 50000) := by
  exact
    packedTile8192 49778944 49795328 11 941 7055 26 _ _ (1772309 / 100000) (221539 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49795328 :
    ThetaLowerSegment 49795328 49811712 (2489358304923 / 50000) (498036843259 / 10000) := by
  exact
    packedTile8192 49795328 49811712 11 932 7056 26 _ _ (886171 / 50000) (354469 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49811712 :
    ThetaLowerSegment 49811712 49828096 (498036843259 / 10000) (996387396893 / 20000) := by
  exact
    packedTile8192 49811712 49828096 11 885 7057 26 _ _ (14179 / 800) (886189 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49828096 :
    ThetaLowerSegment 49828096 49844480 (996387396893 / 20000) (2491793547691 / 50000) := by
  exact
    packedTile8192 49828096 49844480 11 931 7058 26 _ _ (1772407 / 100000) (177241 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49844480 :
    ThetaLowerSegment 49844480 49860864 (2491793547691 / 50000) (2492631025591 / 50000) := by
  exact
    packedTile8192 49844480 49860864 11 945 7060 26 _ _ (44311 / 2500) (1772443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49860864 :
    ThetaLowerSegment 49860864 49877248 (2492631025591 / 50000) (623362033911 / 12500) := by
  exact
    packedTile8192 49860864 49877248 11 922 7061 26 _ _ (1772473 / 100000) (443119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49877248 :
    ThetaLowerSegment 49877248 49893632 (623362033911 / 12500) (498857483447 / 10000) := by
  exact
    packedTile8192 49877248 49893632 11 947 7062 26 _ _ (886253 / 50000) (1772509 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49893632 :
    ThetaLowerSegment 49893632 49910016 (498857483447 / 10000) (4990221523201 / 100000) := by
  exact
    packedTile8192 49893632 49910016 11 929 7063 26 _ _ (1772539 / 100000) (886271 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49910016 :
    ThetaLowerSegment 49910016 49926400 (4990221523201 / 100000) (998367621773 / 20000) := by
  exact
    packedTile8192 49910016 49926400 11 912 7064 26 _ _ (443143 / 25000) (70903 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49926400 :
    ThetaLowerSegment 49926400 49942784 (998367621773 / 20000) (31209391156 / 625) := by
  exact
    packedTile8192 49926400 49942784 11 939 7065 26 _ _ (354521 / 20000) (55394 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49942784 :
    ThetaLowerSegment 49942784 49959168 (31209391156 / 625) (4995085549801 / 100000) := by
  exact
    packedTile8192 49942784 49959168 11 893 7067 26 _ _ (1772637 / 100000) (11079 / 625) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49959168 :
    ThetaLowerSegment 49959168 49975552 (4995085549801 / 100000) (4996771358971 / 100000) := by
  exact
    packedTile8192 49959168 49975552 11 951 7068 26 _ _ (177267 / 10000) (1772673 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49975552 :
    ThetaLowerSegment 49975552 49991936 (4996771358971 / 100000) (4998405791137 / 100000) := by
  exact
    packedTile8192 49975552 49991936 11 922 7069 26 _ _ (1772703 / 100000) (886353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell49991936 :
    ThetaLowerSegment 49991936 50008320 (4998405791137 / 100000) (4999990617121 / 100000) := by
  exact
    packedTile8192 49991936 50008320 11 894 7070 26 _ _ (55398 / 3125) (1772739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50008320 :
    ThetaLowerSegment 50008320 50024704 (4999990617121 / 100000) (5001646382433 / 100000) := by
  exact
    packedTile8192 50008320 50024704 11 934 7071 26 _ _ (55399 / 3125) (1772771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50024704 :
    ThetaLowerSegment 50024704 50041088 (5001646382433 / 100000) (156351032479 / 3125) := by
  exact
    packedTile8192 50024704 50041088 11 895 7072 26 _ _ (1772801 / 100000) (443201 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50041088 :
    ThetaLowerSegment 50041088 50057472 (156351032479 / 3125) (312805775747 / 6250) := by
  exact
    packedTile8192 50041088 50057472 11 936 7073 26 _ _ (886417 / 50000) (1772837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50057472 :
    ThetaLowerSegment 50057472 50073856 (312805775747 / 6250) (2503259951929 / 50000) := by
  exact
    packedTile8192 50057472 50073856 11 918 7075 26 _ _ (1772867 / 100000) (177287 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50073856 :
    ThetaLowerSegment 50073856 50090240 (2503259951929 / 50000) (2504071939671 / 50000) := by
  exact
    packedTile8192 50073856 50090240 11 916 7076 26 _ _ (1772899 / 100000) (886451 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50090240 :
    ThetaLowerSegment 50090240 50106624 (2504071939671 / 50000) (2504915855303 / 50000) := by
  exact
    packedTile8192 50090240 50106624 11 952 7077 26 _ _ (443233 / 25000) (354587 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50106624 :
    ThetaLowerSegment 50106624 50123008 (2504915855303 / 50000) (1252864823119 / 25000) := by
  exact
    packedTile8192 50106624 50123008 11 918 7078 26 _ _ (354593 / 20000) (221621 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50123008 :
    ThetaLowerSegment 50123008 50139392 (1252864823119 / 25000) (2506569160791 / 50000) := by
  exact
    packedTile8192 50123008 50139392 11 947 7079 26 _ _ (886499 / 50000) (1773001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50139392 :
    ThetaLowerSegment 50139392 50155776 (2506569160791 / 50000) (2507377662471 / 50000) := by
  exact
    packedTile8192 50139392 50155776 11 912 7080 26 _ _ (177303 / 10000) (1773033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50155776 :
    ThetaLowerSegment 50155776 50172160 (2507377662471 / 50000) (627044328471 / 12500) := by
  exact
    packedTile8192 50155776 50172160 11 902 7082 26 _ _ (1773063 / 100000) (886533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50172160 :
    ThetaLowerSegment 50172160 50188544 (627044328471 / 12500) (125449735557 / 2500) := by
  exact
    packedTile8192 50172160 50188544 11 922 7083 26 _ _ (221637 / 12500) (1773099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50188544 :
    ThetaLowerSegment 50188544 50204928 (125449735557 / 2500) (125490517501 / 2500) := by
  exact
    packedTile8192 50188544 50204928 11 920 7084 26 _ _ (221641 / 12500) (1773131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50204928 :
    ThetaLowerSegment 50204928 50221312 (125490517501 / 2500) (2510627777241 / 50000) := by
  exact
    packedTile8192 50204928 50221312 11 922 7085 26 _ _ (1773161 / 100000) (443291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50221312 :
    ThetaLowerSegment 50221312 50237696 (2510627777241 / 50000) (2511468271197 / 50000) := by
  exact
    packedTile8192 50221312 50237696 11 948 7086 26 _ _ (886597 / 50000) (1773197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50237696 :
    ThetaLowerSegment 50237696 50254080 (2511468271197 / 50000) (502450762063 / 10000) := by
  exact
    packedTile8192 50237696 50254080 11 886 7087 26 _ _ (886613 / 50000) (1773229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50254080 :
    ThetaLowerSegment 50254080 50270464 (502450762063 / 10000) (2513062416419 / 50000) := by
  exact
    packedTile8192 50254080 50270464 11 912 7089 26 _ _ (1773259 / 100000) (886631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50270464 :
    ThetaLowerSegment 50270464 50286848 (2513062416419 / 50000) (2513899409771 / 50000) := by
  exact
    packedTile8192 50270464 50286848 11 944 7090 26 _ _ (1773291 / 100000) (886647 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50286848 :
    ThetaLowerSegment 50286848 50303232 (2513899409771 / 50000) (2514731098727 / 50000) := by
  exact
    packedTile8192 50286848 50303232 11 938 7091 26 _ _ (443331 / 25000) (1773327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50303232 :
    ThetaLowerSegment 50303232 50319616 (2514731098727 / 50000) (2515557482623 / 50000) := by
  exact
    packedTile8192 50303232 50319616 11 932 7092 26 _ _ (443339 / 25000) (1773359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50319616 :
    ThetaLowerSegment 50319616 50336000 (2515557482623 / 50000) (5032797911407 / 100000) := by
  exact
    packedTile8192 50319616 50336000 11 949 7093 26 _ _ (1773389 / 100000) (110837 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50336000 :
    ThetaLowerSegment 50336000 50352384 (5032797911407 / 100000) (5034434779913 / 100000) := by
  exact
    packedTile8192 50336000 50352384 11 923 7094 26 _ _ (886711 / 50000) (70937 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50352384 :
    ThetaLowerSegment 50352384 50368768 (5034434779913 / 100000) (5036037982329 / 100000) := by
  exact
    packedTile8192 50352384 50368768 11 904 7095 26 _ _ (886727 / 50000) (1773457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50368768 :
    ThetaLowerSegment 50368768 50385152 (5036037982329 / 100000) (5037655402473 / 100000) := by
  exact
    packedTile8192 50368768 50385152 11 912 7097 26 _ _ (1773487 / 100000) (177349 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50385152 :
    ThetaLowerSegment 50385152 50401536 (5037655402473 / 100000) (125981865633 / 2500) := by
  exact
    packedTile8192 50385152 50401536 11 913 7098 26 _ _ (1773519 / 100000) (886761 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50401536 :
    ThetaLowerSegment 50401536 50417920 (125981865633 / 2500) (126021992247 / 2500) := by
  exact
    packedTile8192 50401536 50417920 11 905 7099 26 _ _ (110847 / 6250) (354711 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50417920 :
    ThetaLowerSegment 50417920 50434304 (126021992247 / 2500) (630320130939 / 12500) := by
  exact
    packedTile8192 50417920 50434304 11 948 7100 26 _ _ (110849 / 6250) (1773587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50434304 :
    ThetaLowerSegment 50434304 50450688 (630320130939 / 12500) (2522098161193 / 50000) := by
  exact
    packedTile8192 50434304 50450688 11 922 7101 26 _ _ (1773617 / 100000) (88681 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50450688 :
    ThetaLowerSegment 50450688 50467072 (2522098161193 / 50000) (1261457906691 / 25000) := by
  exact
    packedTile8192 50450688 50467072 11 922 7102 26 _ _ (1773649 / 100000) (443413 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50467072 :
    ThetaLowerSegment 50467072 50483456 (1261457906691 / 25000) (126186496671 / 2500) := by
  exact
    packedTile8192 50467072 50483456 11 918 7104 26 _ _ (886841 / 50000) (354737 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50483456 :
    ThetaLowerSegment 50483456 50499840 (126186496671 / 2500) (631141781607 / 12500) := by
  exact
    packedTile8192 50483456 50499840 11 944 7105 26 _ _ (886857 / 50000) (1773717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50499840 :
    ThetaLowerSegment 50499840 50516224 (631141781607 / 12500) (1262693298771 / 25000) := by
  exact
    packedTile8192 50499840 50516224 11 924 7106 26 _ _ (1773747 / 100000) (1419 / 80) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50516224 :
    ThetaLowerSegment 50516224 50532608 (1262693298771 / 25000) (1263108363057 / 25000) := by
  exact
    packedTile8192 50516224 50532608 11 936 7107 26 _ _ (1773779 / 100000) (886891 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50532608 :
    ThetaLowerSegment 50532608 50548992 (1263108363057 / 25000) (2527027357741 / 50000) := by
  exact
    packedTile8192 50532608 50548992 11 914 7108 26 _ _ (1773811 / 100000) (886907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50548992 :
    ThetaLowerSegment 50548992 50565376 (2527027357741 / 50000) (2527874368251 / 50000) := by
  exact
    packedTile8192 50548992 50565376 11 955 7109 26 _ _ (443461 / 25000) (1773847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50565376 :
    ThetaLowerSegment 50565376 50581760 (2527874368251 / 50000) (2528687690397 / 50000) := by
  exact
    packedTile8192 50565376 50581760 11 917 7110 26 _ _ (443469 / 25000) (1773879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50581760 :
    ThetaLowerSegment 50581760 50598144 (2528687690397 / 50000) (2529514331991 / 50000) := by
  exact
    packedTile8192 50581760 50598144 11 932 7112 26 _ _ (1773909 / 100000) (221739 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50598144 :
    ThetaLowerSegment 50598144 50614528 (2529514331991 / 50000) (5060651819997 / 100000) := by
  exact
    packedTile8192 50598144 50614528 11 915 7113 26 _ _ (1773941 / 100000) (221743 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50614528 :
    ThetaLowerSegment 50614528 50630912 (5060651819997 / 100000) (5062290971049 / 100000) := by
  exact
    packedTile8192 50614528 50630912 11 924 7114 26 _ _ (1773973 / 100000) (221747 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50630912 :
    ThetaLowerSegment 50630912 50647296 (5062290971049 / 100000) (5063930152593 / 100000) := by
  exact
    packedTile8192 50630912 50647296 11 924 7115 26 _ _ (887003 / 50000) (1774009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50647296 :
    ThetaLowerSegment 50647296 50663680 (5063930152593 / 100000) (5065535656983 / 100000) := by
  exact
    packedTile8192 50647296 50663680 11 905 7116 26 _ _ (887019 / 50000) (1774041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50663680 :
    ThetaLowerSegment 50663680 50680064 (5065535656983 / 100000) (5067201508713 / 100000) := by
  exact
    packedTile8192 50663680 50680064 11 939 7117 26 _ _ (177407 / 10000) (1774073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50680064 :
    ThetaLowerSegment 50680064 50696448 (5067201508713 / 100000) (5068826587061 / 100000) := by
  exact
    packedTile8192 50680064 50696448 11 916 7118 26 _ _ (1774103 / 100000) (887053 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50696448 :
    ThetaLowerSegment 50696448 50712832 (5068826587061 / 100000) (5070441049911 / 100000) := by
  exact
    packedTile8192 50696448 50712832 11 910 7120 26 _ _ (354827 / 20000) (887069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50712832 :
    ThetaLowerSegment 50712832 50729216 (5070441049911 / 100000) (1014415366377 / 20000) := by
  exact
    packedTile8192 50712832 50729216 11 922 7121 26 _ _ (1774167 / 100000) (177417 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50729216 :
    ThetaLowerSegment 50729216 50745600 (1014415366377 / 20000) (1014750690177 / 20000) := by
  exact
    packedTile8192 50729216 50745600 11 945 7122 26 _ _ (8871 / 500) (1774203 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50745600 :
    ThetaLowerSegment 50745600 50761984 (1014750690177 / 20000) (1015089568489 / 20000) := by
  exact
    packedTile8192 50745600 50761984 11 955 7123 26 _ _ (221779 / 12500) (354847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50761984 :
    ThetaLowerSegment 50761984 50778368 (1015089568489 / 20000) (5077057099893 / 100000) := by
  exact
    packedTile8192 50761984 50778368 11 907 7124 26 _ _ (221783 / 12500) (1774267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50778368 :
    ThetaLowerSegment 50778368 50794752 (5077057099893 / 100000) (1015740019783 / 20000) := by
  exact
    packedTile8192 50778368 50794752 11 926 7125 26 _ _ (1774297 / 100000) (17743 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50794752 :
    ThetaLowerSegment 50794752 50811136 (1015740019783 / 20000) (2540165353633 / 50000) := by
  exact
    packedTile8192 50794752 50811136 11 919 7127 26 _ _ (1774329 / 100000) (443583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50811136 :
    ThetaLowerSegment 50811136 50827520 (2540165353633 / 50000) (5082000380967 / 100000) := by
  exact
    packedTile8192 50811136 50827520 11 941 7128 26 _ _ (1774361 / 100000) (443591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50827520 :
    ThetaLowerSegment 50827520 50843904 (5082000380967 / 100000) (1270913972409 / 25000) := by
  exact
    packedTile8192 50827520 50843904 11 933 7129 26 _ _ (1774393 / 100000) (443599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50843904 :
    ThetaLowerSegment 50843904 50860288 (1270913972409 / 25000) (1271325639241 / 25000) := by
  exact
    packedTile8192 50843904 50860288 11 928 7130 26 _ _ (887213 / 50000) (1774429 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50860288 :
    ThetaLowerSegment 50860288 50876672 (1271325639241 / 25000) (2543466641933 / 50000) := by
  exact
    packedTile8192 50860288 50876672 11 919 7131 26 _ _ (887229 / 50000) (1774461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50876672 :
    ThetaLowerSegment 50876672 50893056 (2543466641933 / 50000) (2544272260393 / 50000) := by
  exact
    packedTile8192 50876672 50893056 11 908 7132 26 _ _ (177449 / 10000) (1774493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50893056 :
    ThetaLowerSegment 50893056 50909440 (2544272260393 / 50000) (254508587873 / 5000) := by
  exact
    packedTile8192 50893056 50909440 11 917 7133 26 _ _ (887261 / 50000) (70981 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50909440 :
    ThetaLowerSegment 50909440 50925824 (254508587873 / 5000) (2545910159063 / 50000) := by
  exact
    packedTile8192 50909440 50925824 11 929 7135 26 _ _ (887277 / 50000) (1774557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50925824 :
    ThetaLowerSegment 50925824 50942208 (2545910159063 / 50000) (5093405024317 / 100000) := by
  exact
    packedTile8192 50925824 50942208 11 893 7136 26 _ _ (1774587 / 100000) (177459 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50942208 :
    ThetaLowerSegment 50942208 50958592 (5093405024317 / 100000) (4076011683 / 80) := by
  exact
    packedTile8192 50942208 50958592 11 907 7137 26 _ _ (1774619 / 100000) (887311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50958592 :
    ThetaLowerSegment 50958592 50974976 (4076011683 / 80) (5096645508019 / 100000) := by
  exact
    packedTile8192 50958592 50974976 11 919 7138 26 _ _ (1774651 / 100000) (887327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50974976 :
    ThetaLowerSegment 50974976 50991360 (5096645508019 / 100000) (5098271117647 / 100000) := by
  exact
    packedTile8192 50974976 50991360 11 916 7139 26 _ _ (1774683 / 100000) (887343 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell50991360 :
    ThetaLowerSegment 50991360 51007744 (5098271117647 / 100000) (5099942899177 / 100000) := by
  exact
    packedTile8192 50991360 51007744 11 942 7140 26 _ _ (354943 / 20000) (887359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51007744 :
    ThetaLowerSegment 51007744 51024128 (5099942899177 / 100000) (1020309454093 / 20000) := by
  exact
    packedTile8192 51007744 51024128 11 904 7141 26 _ _ (1774747 / 100000) (7099 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51024128 :
    ThetaLowerSegment 51024128 51040512 (1020309454093 / 20000) (2551582047067 / 50000) := by
  exact
    packedTile8192 51024128 51040512 11 911 7143 26 _ _ (1774779 / 100000) (887391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51040512 :
    ThetaLowerSegment 51040512 51056896 (2551582047067 / 50000) (2552384262091 / 50000) := by
  exact
    packedTile8192 51040512 51056896 11 904 7144 26 _ _ (443703 / 25000) (354963 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51056896 :
    ThetaLowerSegment 51056896 51073280 (2552384262091 / 50000) (2553203352597 / 50000) := by
  exact
    packedTile8192 51056896 51073280 11 923 7145 26 _ _ (443711 / 25000) (1774847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51073280 :
    ThetaLowerSegment 51073280 51089664 (2553203352597 / 50000) (510804136599 / 10000) := by
  exact
    packedTile8192 51073280 51089664 11 921 7146 26 _ _ (443719 / 25000) (1774879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51089664 :
    ThetaLowerSegment 51089664 51106048 (510804136599 / 10000) (2554849565031 / 50000) := by
  exact
    packedTile8192 51089664 51106048 11 934 7147 26 _ _ (443727 / 25000) (1774911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51106048 :
    ThetaLowerSegment 51106048 51122432 (2554849565031 / 50000) (2555698873821 / 50000) := by
  exact
    packedTile8192 51106048 51122432 11 957 7148 26 _ _ (88747 / 5000) (1774943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51122432 :
    ThetaLowerSegment 51122432 51138816 (2555698873821 / 50000) (2556503823623 / 50000) := by
  exact
    packedTile8192 51122432 51138816 11 907 7149 26 _ _ (443743 / 25000) (70999 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51138816 :
    ThetaLowerSegment 51138816 51155200 (2556503823623 / 50000) (2557310562941 / 50000) := by
  exact
    packedTile8192 51138816 51155200 11 909 7151 26 _ _ (443751 / 25000) (1775007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51155200 :
    ThetaLowerSegment 51155200 51171584 (2557310562941 / 50000) (2558114654249 / 50000) := by
  exact
    packedTile8192 51155200 51171584 11 906 7152 26 _ _ (443759 / 25000) (1775039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51171584 :
    ThetaLowerSegment 51171584 51187968 (2558114654249 / 50000) (2558944498539 / 50000) := by
  exact
    packedTile8192 51171584 51187968 11 935 7153 26 _ _ (443767 / 25000) (1775071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51187968 :
    ThetaLowerSegment 51187968 51204352 (2558944498539 / 50000) (2559769032489 / 50000) := by
  exact
    packedTile8192 51187968 51204352 11 929 7154 26 _ _ (17751 / 1000) (1775103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51204352 :
    ThetaLowerSegment 51204352 51220736 (2559769032489 / 50000) (512114633457 / 10000) := by
  exact
    packedTile8192 51204352 51220736 11 906 7155 26 _ _ (443783 / 25000) (355027 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51220736 :
    ThetaLowerSegment 51220736 51237120 (512114633457 / 10000) (2561397730963 / 50000) := by
  exact
    packedTile8192 51220736 51237120 11 929 7156 26 _ _ (443791 / 25000) (1775167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51237120 :
    ThetaLowerSegment 51237120 51253504 (2561397730963 / 50000) (2562224084701 / 50000) := by
  exact
    packedTile8192 51237120 51253504 11 931 7158 26 _ _ (443799 / 25000) (1775199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51253504 :
    ThetaLowerSegment 51253504 51269888 (2562224084701 / 50000) (2563046902879 / 50000) := by
  exact
    packedTile8192 51253504 51269888 11 927 7159 26 _ _ (443807 / 25000) (1775231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51269888 :
    ThetaLowerSegment 51269888 51286272 (2563046902879 / 50000) (2563853758549 / 50000) := by
  exact
    packedTile8192 51269888 51286272 11 909 7160 26 _ _ (88763 / 5000) (1775263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51286272 :
    ThetaLowerSegment 51286272 51302656 (2563853758549 / 50000) (2564661516409 / 50000) := by
  exact
    packedTile8192 51286272 51302656 11 910 7161 26 _ _ (443823 / 25000) (355059 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51302656 :
    ThetaLowerSegment 51302656 51319040 (2564661516409 / 50000) (513097053349 / 10000) := by
  exact
    packedTile8192 51302656 51319040 11 928 7162 26 _ _ (443831 / 25000) (1775327 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51319040 :
    ThetaLowerSegment 51319040 51335424 (513097053349 / 10000) (2566299267471 / 50000) := by
  exact
    packedTile8192 51319040 51335424 11 917 7163 26 _ _ (443839 / 25000) (1775359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51335424 :
    ThetaLowerSegment 51335424 51351808 (2566299267471 / 50000) (2567131924443 / 50000) := by
  exact
    packedTile8192 51335424 51351808 11 938 7164 26 _ _ (443847 / 25000) (1775391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51351808 :
    ThetaLowerSegment 51351808 51368192 (2567131924443 / 50000) (2567963708713 / 50000) := by
  exact
    packedTile8192 51351808 51368192 11 937 7166 26 _ _ (88771 / 5000) (1775423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51368192 :
    ThetaLowerSegment 51368192 51384576 (2567963708713 / 50000) (1284407074871 / 25000) := by
  exact
    packedTile8192 51368192 51384576 11 958 7167 26 _ _ (1775451 / 100000) (887727 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51384576 :
    ThetaLowerSegment 51384576 51400960 (1284407074871 / 25000) (513930080447 / 10000) := by
  exact
    packedTile8192 51384576 51400960 11 942 7168 26 _ _ (1775483 / 100000) (887743 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51400960 :
    ThetaLowerSegment 51400960 51417344 (513930080447 / 10000) (205636447863 / 4000) := by
  exact
    packedTile8192 51400960 51417344 11 907 7169 26 _ _ (355103 / 20000) (887759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51417344 :
    ThetaLowerSegment 51417344 51433728 (205636447863 / 4000) (2571287442057 / 50000) := by
  exact
    packedTile8192 51417344 51433728 11 937 7170 26 _ _ (1775547 / 100000) (35511 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51433728 :
    ThetaLowerSegment 51433728 51450112 (2571287442057 / 50000) (5144160476161 / 100000) := by
  exact
    packedTile8192 51433728 51450112 11 893 7171 26 _ _ (1775579 / 100000) (887791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51450112 :
    ThetaLowerSegment 51450112 51466496 (5144160476161 / 100000) (643216486487 / 12500) := by
  exact
    packedTile8192 51450112 51466496 11 885 7172 26 _ _ (1775611 / 100000) (887807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51466496 :
    ThetaLowerSegment 51466496 51482880 (643216486487 / 12500) (5147363707813 / 100000) := by
  exact
    packedTile8192 51466496 51482880 11 919 7174 26 _ _ (1775643 / 100000) (887823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51482880 :
    ThetaLowerSegment 51482880 51499264 (5147363707813 / 100000) (5149032841373 / 100000) := by
  exact
    packedTile8192 51482880 51499264 11 940 7175 26 _ _ (887837 / 50000) (1775677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51499264 :
    ThetaLowerSegment 51499264 51515648 (5149032841373 / 100000) (5150703780719 / 100000) := by
  exact
    packedTile8192 51499264 51515648 11 941 7176 26 _ _ (887853 / 50000) (1775709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51515648 :
    ThetaLowerSegment 51515648 51532032 (5150703780719 / 100000) (206094705889 / 4000) := by
  exact
    packedTile8192 51515648 51532032 11 937 7177 26 _ _ (887869 / 50000) (1775741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51532032 :
    ThetaLowerSegment 51532032 51548416 (206094705889 / 4000) (1030795654123 / 20000) := by
  exact
    packedTile8192 51532032 51548416 11 907 7178 26 _ _ (177577 / 10000) (1775773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51548416 :
    ThetaLowerSegment 51548416 51564800 (1030795654123 / 20000) (5155636869683 / 100000) := by
  exact
    packedTile8192 51548416 51564800 11 934 7179 26 _ _ (887901 / 50000) (355161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51564800 :
    ThetaLowerSegment 51564800 51581184 (5155636869683 / 100000) (5157341669363 / 100000) := by
  exact
    packedTile8192 51564800 51581184 11 960 7180 26 _ _ (1775833 / 100000) (443959 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51581184 :
    ThetaLowerSegment 51581184 51597568 (5157341669363 / 100000) (1289737206797 / 25000) := by
  exact
    packedTile8192 51581184 51597568 11 905 7182 26 _ _ (355173 / 20000) (443967 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51597568 :
    ThetaLowerSegment 51597568 51613952 (1289737206797 / 25000) (5160616394471 / 100000) := by
  exact
    packedTile8192 51597568 51613952 11 939 7183 26 _ _ (1775897 / 100000) (17759 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51613952 :
    ThetaLowerSegment 51613952 51630336 (5160616394471 / 100000) (5162232489861 / 100000) := by
  exact
    packedTile8192 51613952 51630336 11 910 7184 26 _ _ (1775929 / 100000) (443983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51630336 :
    ThetaLowerSegment 51630336 51646720 (5162232489861 / 100000) (5163825525981 / 100000) := by
  exact
    packedTile8192 51630336 51646720 11 897 7185 26 _ _ (44399 / 2500) (1775963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51646720 :
    ThetaLowerSegment 51646720 51663104 (5163825525981 / 100000) (1033089046137 / 20000) := by
  exact
    packedTile8192 51646720 51663104 11 912 7186 26 _ _ (221999 / 12500) (355199 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51663104 :
    ThetaLowerSegment 51663104 51679488 (1033089046137 / 20000) (5167066740597 / 100000) := by
  exact
    packedTile8192 51663104 51679488 11 913 7187 26 _ _ (222003 / 12500) (1776027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51679488 :
    ThetaLowerSegment 51679488 51695872 (5167066740597 / 100000) (206747531189 / 4000) := by
  exact
    packedTile8192 51679488 51695872 11 913 7188 26 _ _ (222007 / 12500) (1776059 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51695872 :
    ThetaLowerSegment 51695872 51712256 (206747531189 / 4000) (1034068008127 / 20000) := by
  exact
    packedTile8192 51695872 51712256 11 930 7189 26 _ _ (1776087 / 100000) (177609 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51712256 :
    ThetaLowerSegment 51712256 51728640 (1034068008127 / 20000) (5171945652211 / 100000) := by
  exact
    packedTile8192 51712256 51728640 11 904 7191 26 _ _ (1776119 / 100000) (888061 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51728640 :
    ThetaLowerSegment 51728640 51745024 (5171945652211 / 100000) (5173625891057 / 100000) := by
  exact
    packedTile8192 51728640 51745024 11 946 7192 26 _ _ (1776151 / 100000) (888077 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51745024 :
    ThetaLowerSegment 51745024 51761408 (5173625891057 / 100000) (5175288397409 / 100000) := by
  exact
    packedTile8192 51745024 51761408 11 936 7193 26 _ _ (888091 / 50000) (355237 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51761408 :
    ThetaLowerSegment 51761408 51777792 (5175288397409 / 100000) (5176926066717 / 100000) := by
  exact
    packedTile8192 51761408 51777792 11 922 7194 26 _ _ (888107 / 50000) (1776217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51777792 :
    ThetaLowerSegment 51777792 51794176 (5176926066717 / 100000) (5178572646759 / 100000) := by
  exact
    packedTile8192 51777792 51794176 11 927 7195 26 _ _ (888123 / 50000) (1776249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51794176 :
    ThetaLowerSegment 51794176 51810560 (5178572646759 / 100000) (2590134495647 / 50000) := by
  exact
    packedTile8192 51794176 51810560 11 955 7196 26 _ _ (1776277 / 100000) (44407 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51810560 :
    ThetaLowerSegment 51810560 51826944 (2590134495647 / 50000) (518194582699 / 10000) := by
  exact
    packedTile8192 51810560 51826944 11 944 7197 26 _ _ (1776309 / 100000) (222039 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51826944 :
    ThetaLowerSegment 51826944 51843328 (518194582699 / 10000) (323977528519 / 6250) := by
  exact
    packedTile8192 51826944 51843328 11 954 7199 26 _ _ (1776341 / 100000) (222043 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51843328 :
    ThetaLowerSegment 51843328 51859712 (323977528519 / 6250) (324077005351 / 6250) := by
  exact
    packedTile8192 51843328 51859712 11 896 7200 26 _ _ (444093 / 25000) (14211 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51859712 :
    ThetaLowerSegment 51859712 51876096 (324077005351 / 6250) (259342519483 / 5000) := by
  exact
    packedTile8192 51859712 51876096 11 911 7201 26 _ _ (444101 / 25000) (1776407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51876096 :
    ThetaLowerSegment 51876096 51892480 (259342519483 / 5000) (518848826273 / 10000) := by
  exact
    packedTile8192 51876096 51892480 11 922 7202 26 _ _ (355287 / 20000) (888219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51892480 :
    ThetaLowerSegment 51892480 51908864 (518848826273 / 10000) (5190092412431 / 100000) := by
  exact
    packedTile8192 51892480 51908864 11 903 7203 26 _ _ (1776467 / 100000) (177647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51908864 :
    ThetaLowerSegment 51908864 51925248 (5190092412431 / 100000) (5191776533483 / 100000) := by
  exact
    packedTile8192 51908864 51925248 11 948 7204 26 _ _ (1776499 / 100000) (888251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51925248 :
    ThetaLowerSegment 51925248 51941632 (5191776533483 / 100000) (5193400281903 / 100000) := by
  exact
    packedTile8192 51925248 51941632 11 914 7205 26 _ _ (177653 / 10000) (1776533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51941632 :
    ThetaLowerSegment 51941632 51958016 (5193400281903 / 100000) (5195073803307 / 100000) := by
  exact
    packedTile8192 51941632 51958016 11 942 7207 26 _ _ (888281 / 50000) (355313 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51958016 :
    ThetaLowerSegment 51958016 51974400 (5195073803307 / 100000) (649586090793 / 12500) := by
  exact
    packedTile8192 51958016 51974400 11 909 7208 26 _ _ (1776593 / 100000) (444149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51974400 :
    ThetaLowerSegment 51974400 51990784 (649586090793 / 12500) (2599152727547 / 50000) := by
  exact
    packedTile8192 51974400 51990784 11 910 7209 26 _ _ (14213 / 800) (444157 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell51990784 :
    ThetaLowerSegment 51990784 52007168 (2599152727547 / 50000) (2599954887731 / 50000) := by
  exact
    packedTile8192 51990784 52007168 11 903 7210 26 _ _ (111041 / 6250) (1776659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52007168 :
    ThetaLowerSegment 52007168 52023552 (2599954887731 / 50000) (2600784601027 / 50000) := by
  exact
    packedTile8192 52007168 52023552 11 934 7211 26 _ _ (111043 / 6250) (1776691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52023552 :
    ThetaLowerSegment 52023552 52039936 (2600784601027 / 50000) (5203209113691 / 100000) := by
  exact
    packedTile8192 52023552 52039936 11 923 7212 26 _ _ (1776719 / 100000) (888361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52039936 :
    ThetaLowerSegment 52039936 52056320 (5203209113691 / 100000) (5204857938619 / 100000) := by
  exact
    packedTile8192 52039936 52056320 11 928 7213 26 _ _ (1776751 / 100000) (888377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52056320 :
    ThetaLowerSegment 52056320 52072704 (5204857938619 / 100000) (5206558318993 / 100000) := by
  exact
    packedTile8192 52056320 52072704 11 957 7215 26 _ _ (888391 / 50000) (355357 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52072704 :
    ThetaLowerSegment 52072704 52089088 (5206558318993 / 100000) (5208169889291 / 100000) := by
  exact
    packedTile8192 52072704 52089088 11 907 7216 26 _ _ (888407 / 50000) (1776817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52089088 :
    ThetaLowerSegment 52089088 52105472 (5208169889291 / 100000) (1302453367729 / 25000) := by
  exact
    packedTile8192 52089088 52105472 11 925 7217 26 _ _ (355369 / 20000) (111053 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52105472 :
    ThetaLowerSegment 52105472 52121856 (1302453367729 / 25000) (2605711660739 / 50000) := by
  exact
    packedTile8192 52105472 52121856 11 906 7218 26 _ _ (1776877 / 100000) (22211 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52121856 :
    ThetaLowerSegment 52121856 52138240 (2605711660739 / 50000) (2606521930787 / 50000) := by
  exact
    packedTile8192 52121856 52138240 11 912 7219 26 _ _ (444227 / 25000) (1776911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52138240 :
    ThetaLowerSegment 52138240 52154624 (2606521930787 / 50000) (5214680422393 / 100000) := by
  exact
    packedTile8192 52138240 52154624 11 921 7220 26 _ _ (1776939 / 100000) (888471 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52154624 :
    ThetaLowerSegment 52154624 52171008 (5214680422393 / 100000) (2608138959661 / 50000) := by
  exact
    packedTile8192 52154624 52171008 11 899 7221 26 _ _ (1776971 / 100000) (888487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52171008 :
    ThetaLowerSegment 52171008 52187392 (2608138959661 / 50000) (652245092527 / 12500) := by
  exact
    packedTile8192 52171008 52187392 11 947 7222 26 _ _ (888501 / 50000) (355401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52187392 :
    ThetaLowerSegment 52187392 52203776 (652245092527 / 12500) (652445897369 / 12500) := by
  exact
    packedTile8192 52187392 52203776 11 904 7224 26 _ _ (888517 / 50000) (1777037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52203776 :
    ThetaLowerSegment 52203776 52220160 (652445897369 / 12500) (5221218072337 / 100000) := by
  exact
    packedTile8192 52203776 52220160 11 929 7225 26 _ _ (355413 / 20000) (444267 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52220160 :
    ThetaLowerSegment 52220160 52236544 (5221218072337 / 100000) (5222872548713 / 100000) := by
  exact
    packedTile8192 52220160 52236544 11 931 7226 26 _ _ (222137 / 12500) (1777099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52236544 :
    ThetaLowerSegment 52236544 52252928 (5222872548713 / 100000) (5224471963913 / 100000) := by
  exact
    packedTile8192 52236544 52252928 11 900 7227 26 _ _ (222141 / 12500) (1777131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52252928 :
    ThetaLowerSegment 52252928 52269312 (5224471963913 / 100000) (522611228167 / 10000) := by
  exact
    packedTile8192 52252928 52269312 11 923 7228 26 _ _ (1777159 / 100000) (888581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52269312 :
    ThetaLowerSegment 52269312 52285696 (522611228167 / 10000) (52277064211 / 1000) := by
  exact
    packedTile8192 52269312 52285696 11 897 7229 26 _ _ (177719 / 10000) (1777193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52285696 :
    ThetaLowerSegment 52285696 52302080 (52277064211 / 1000) (2614652071839 / 50000) := by
  exact
    packedTile8192 52285696 52302080 11 899 7230 26 _ _ (888611 / 50000) (71089 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52302080 :
    ThetaLowerSegment 52302080 52318464 (2614652071839 / 50000) (5230951657209 / 100000) := by
  exact
    packedTile8192 52302080 52318464 11 927 7232 26 _ _ (1777253 / 100000) (222157 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52318464 :
    ThetaLowerSegment 52318464 52334848 (5230951657209 / 100000) (5232577872069 / 100000) := by
  exact
    packedTile8192 52318464 52334848 11 915 7233 26 _ _ (444321 / 25000) (1777287 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52334848 :
    ThetaLowerSegment 52334848 52351232 (5232577872069 / 100000) (5234266322269 / 100000) := by
  exact
    packedTile8192 52334848 52351232 11 950 7234 26 _ _ (444329 / 25000) (1777319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52351232 :
    ThetaLowerSegment 52351232 52367616 (5234266322269 / 100000) (2617967625551 / 50000) := by
  exact
    packedTile8192 52351232 52367616 11 939 7235 26 _ _ (1777347 / 100000) (35547 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52367616 :
    ThetaLowerSegment 52367616 52384000 (2617967625551 / 50000) (654695638341 / 12500) := by
  exact
    packedTile8192 52367616 52384000 11 917 7236 26 _ _ (888689 / 50000) (1777381 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52384000 :
    ThetaLowerSegment 52384000 52400384 (654695638341 / 12500) (654901817901 / 12500) := by
  exact
    packedTile8192 52384000 52400384 11 928 7237 26 _ _ (177741 / 10000) (1777413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52400384 :
    ThetaLowerSegment 52400384 52416768 (654901817901 / 12500) (5240869340779 / 100000) := by
  exact
    packedTile8192 52400384 52416768 11 931 7238 26 _ _ (1777441 / 100000) (444361 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52416768 :
    ThetaLowerSegment 52416768 52433152 (5240869340779 / 100000) (5242433516139 / 100000) := by
  exact
    packedTile8192 52416768 52433152 11 880 7239 26 _ _ (55546 / 3125) (71099 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52433152 :
    ThetaLowerSegment 52433152 52449536 (5242433516139 / 100000) (163878205983 / 3125) := by
  exact
    packedTile8192 52433152 52449536 11 939 7241 26 _ _ (1777503 / 100000) (888753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52449536 :
    ThetaLowerSegment 52449536 52465920 (163878205983 / 3125) (1311432703379 / 25000) := by
  exact
    packedTile8192 52449536 52465920 11 916 7242 26 _ _ (355507 / 20000) (888769 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52465920 :
    ThetaLowerSegment 52465920 52482304 (1311432703379 / 25000) (163980081847 / 3125) := by
  exact
    packedTile8192 52465920 52482304 11 918 7243 26 _ _ (888783 / 50000) (1777569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52482304 :
    ThetaLowerSegment 52482304 52498688 (163980081847 / 3125) (2624511447351 / 50000) := by
  exact
    packedTile8192 52482304 52498688 11 934 7244 26 _ _ (1777597 / 100000) (2222 / 125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52498688 :
    ThetaLowerSegment 52498688 52515072 (2624511447351 / 50000) (525064231381 / 10000) := by
  exact
    packedTile8192 52498688 52515072 11 911 7245 26 _ _ (444407 / 25000) (1777631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52515072 :
    ThetaLowerSegment 52515072 52531456 (525064231381 / 10000) (105044986369 / 2000) := by
  exact
    packedTile8192 52515072 52531456 11 904 7246 26 _ _ (88883 / 5000) (1777663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52531456 :
    ThetaLowerSegment 52531456 52547840 (105044986369 / 2000) (5253879461097 / 100000) := by
  exact
    packedTile8192 52531456 52547840 11 917 7247 26 _ _ (1777691 / 100000) (888847 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52547840 :
    ThetaLowerSegment 52547840 52564224 (5253879461097 / 100000) (5255550519777 / 100000) := by
  exact
    packedTile8192 52547840 52564224 11 940 7248 26 _ _ (888861 / 50000) (71109 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52564224 :
    ThetaLowerSegment 52564224 52580608 (5255550519777 / 100000) (1051428677293 / 20000) := by
  exact
    packedTile8192 52564224 52580608 11 896 7250 26 _ _ (1777753 / 100000) (444439 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52580608 :
    ThetaLowerSegment 52580608 52596992 (1051428677293 / 20000) (1051759345117 / 20000) := by
  exact
    packedTile8192 52580608 52596992 11 930 7251 26 _ _ (222223 / 12500) (1777787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52596992 :
    ThetaLowerSegment 52596992 52613376 (1051759345117 / 20000) (1052094285463 / 20000) := by
  exact
    packedTile8192 52596992 52613376 11 942 7252 26 _ _ (355563 / 20000) (888909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52613376 :
    ThetaLowerSegment 52613376 52629760 (1052094285463 / 20000) (5262117713637 / 100000) := by
  exact
    packedTile8192 52613376 52629760 11 926 7253 26 _ _ (1777847 / 100000) (35557 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52629760 :
    ThetaLowerSegment 52629760 52646144 (5262117713637 / 100000) (5263824476517 / 100000) := by
  exact
    packedTile8192 52629760 52646144 11 960 7254 26 _ _ (888939 / 50000) (1777881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52646144 :
    ThetaLowerSegment 52646144 52662528 (5263824476517 / 100000) (5265435262071 / 100000) := by
  exact
    packedTile8192 52646144 52662528 11 906 7255 26 _ _ (1777909 / 100000) (222239 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52662528 :
    ThetaLowerSegment 52662528 52678912 (5265435262071 / 100000) (5267037186011 / 100000) := by
  exact
    packedTile8192 52662528 52678912 11 901 7256 26 _ _ (88897 / 5000) (1777943 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52678912 :
    ThetaLowerSegment 52678912 52695296 (5267037186011 / 100000) (5268655139621 / 100000) := by
  exact
    packedTile8192 52678912 52695296 11 910 7258 26 _ _ (1777971 / 100000) (888987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52695296 :
    ThetaLowerSegment 52695296 52711680 (5268655139621 / 100000) (5270287345457 / 100000) := by
  exact
    packedTile8192 52695296 52711680 11 918 7259 26 _ _ (889001 / 50000) (355601 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52711680 :
    ThetaLowerSegment 52711680 52728064 (5270287345457 / 100000) (5271937360081 / 100000) := by
  exact
    packedTile8192 52711680 52728064 11 928 7260 26 _ _ (1778033 / 100000) (444509 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52728064 :
    ThetaLowerSegment 52728064 52744448 (5271937360081 / 100000) (5273578513153 / 100000) := by
  exact
    packedTile8192 52728064 52744448 11 923 7261 26 _ _ (111129 / 6250) (1778067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52744448 :
    ThetaLowerSegment 52744448 52760832 (5273578513153 / 100000) (5275171686273 / 100000) := by
  exact
    packedTile8192 52744448 52760832 11 896 7262 26 _ _ (355619 / 20000) (889049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52760832 :
    ThetaLowerSegment 52760832 52777216 (5275171686273 / 100000) (5276860905973 / 100000) := by
  exact
    packedTile8192 52760832 52777216 11 950 7263 26 _ _ (889063 / 50000) (1778129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52777216 :
    ThetaLowerSegment 52777216 52793600 (5276860905973 / 100000) (5278514592913 / 100000) := by
  exact
    packedTile8192 52777216 52793600 11 930 7264 26 _ _ (889079 / 50000) (1778161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52793600 :
    ThetaLowerSegment 52793600 52809984 (5278514592913 / 100000) (1320040743529 / 25000) := by
  exact
    packedTile8192 52793600 52809984 11 927 7265 26 _ _ (1778189 / 100000) (111137 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52809984 :
    ThetaLowerSegment 52809984 52826368 (1320040743529 / 25000) (1320455068789 / 25000) := by
  exact
    packedTile8192 52809984 52826368 11 932 7267 26 _ _ (88911 / 5000) (1778223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52826368 :
    ThetaLowerSegment 52826368 52842752 (1320455068789 / 25000) (5283429592311 / 100000) := by
  exact
    packedTile8192 52826368 52842752 11 905 7268 26 _ _ (1778251 / 100000) (889127 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52842752 :
    ThetaLowerSegment 52842752 52859136 (5283429592311 / 100000) (5285035380957 / 100000) := by
  exact
    packedTile8192 52842752 52859136 11 903 7269 26 _ _ (889141 / 50000) (355657 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52859136 :
    ThetaLowerSegment 52859136 52875520 (5285035380957 / 100000) (21146977359 / 400) := by
  exact
    packedTile8192 52859136 52875520 11 961 7270 26 _ _ (1778313 / 100000) (444579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52875520 :
    ThetaLowerSegment 52875520 52891904 (21146977359 / 400) (2644177759707 / 50000) := by
  exact
    packedTile8192 52875520 52891904 11 906 7271 26 _ _ (222293 / 12500) (1778347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52891904 :
    ThetaLowerSegment 52891904 52908288 (2644177759707 / 50000) (330624254229 / 6250) := by
  exact
    packedTile8192 52891904 52908288 11 918 7272 26 _ _ (14227 / 800) (889189 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52908288 :
    ThetaLowerSegment 52908288 52924672 (330624254229 / 6250) (1322912274717 / 25000) := by
  exact
    packedTile8192 52908288 52924672 11 934 7273 26 _ _ (889203 / 50000) (1778409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52924672 :
    ThetaLowerSegment 52924672 52941056 (1322912274717 / 25000) (211730770199 / 4000) := by
  exact
    packedTile8192 52924672 52941056 11 911 7274 26 _ _ (1778437 / 100000) (44461 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52941056 :
    ThetaLowerSegment 52941056 52957440 (211730770199 / 4000) (529487876761 / 10000) := by
  exact
    packedTile8192 52941056 52957440 11 905 7276 26 _ _ (1778467 / 100000) (177847 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52957440 :
    ThetaLowerSegment 52957440 52973824 (529487876761 / 10000) (2648255714387 / 50000) := by
  exact
    packedTile8192 52957440 52973824 11 918 7277 26 _ _ (889249 / 50000) (1778501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52973824 :
    ThetaLowerSegment 52973824 52990208 (2648255714387 / 50000) (5298195695737 / 100000) := by
  exact
    packedTile8192 52973824 52990208 11 947 7278 26 _ _ (1778529 / 100000) (444633 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell52990208 :
    ThetaLowerSegment 52990208 53006592 (5298195695737 / 100000) (5299810628217 / 100000) := by
  exact
    packedTile8192 52990208 53006592 11 908 7279 26 _ _ (11116 / 625) (1778563 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53006592 :
    ThetaLowerSegment 53006592 53022976 (5299810628217 / 100000) (5301432703209 / 100000) := by
  exact
    packedTile8192 53006592 53022976 11 912 7280 26 _ _ (1778591 / 100000) (889297 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53022976 :
    ThetaLowerSegment 53022976 53039360 (5301432703209 / 100000) (5303095714779 / 100000) := by
  exact
    packedTile8192 53022976 53039360 11 935 7281 26 _ _ (889311 / 50000) (14229 / 800) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53039360 :
    ThetaLowerSegment 53039360 53055744 (5303095714779 / 100000) (2652368705749 / 50000) := by
  exact
    packedTile8192 53039360 53055744 11 923 7282 26 _ _ (1778653 / 100000) (55583 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53055744 :
    ThetaLowerSegment 53055744 53072128 (2652368705749 / 50000) (2653172670917 / 50000) := by
  exact
    packedTile8192 53055744 53072128 11 904 7283 26 _ _ (444671 / 25000) (1778687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53072128 :
    ThetaLowerSegment 53072128 53088512 (2653172670917 / 50000) (2654008666967 / 50000) := by
  exact
    packedTile8192 53072128 53088512 11 940 7285 26 _ _ (355743 / 20000) (889359 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53088512 :
    ThetaLowerSegment 53088512 53104896 (2654008666967 / 50000) (2654830447619 / 50000) := by
  exact
    packedTile8192 53088512 53104896 11 924 7286 26 _ _ (889373 / 50000) (1778749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53104896 :
    ThetaLowerSegment 53104896 53121280 (2654830447619 / 50000) (2655634454371 / 50000) := by
  exact
    packedTile8192 53104896 53121280 11 904 7287 26 _ _ (222347 / 12500) (1778779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53121280 :
    ThetaLowerSegment 53121280 53137664 (2655634454371 / 50000) (5312932093287 / 100000) := by
  exact
    packedTile8192 53121280 53137664 11 935 7288 26 _ _ (1778807 / 100000) (177881 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53137664 :
    ThetaLowerSegment 53137664 53154048 (5312932093287 / 100000) (1062917638293 / 20000) := by
  exact
    packedTile8192 53137664 53154048 11 931 7289 26 _ _ (889419 / 50000) (1778841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53154048 :
    ThetaLowerSegment 53154048 53170432 (1062917638293 / 20000) (5316253212849 / 100000) := by
  exact
    packedTile8192 53154048 53170432 11 936 7290 26 _ _ (1778869 / 100000) (222359 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53170432 :
    ThetaLowerSegment 53170432 53186816 (5316253212849 / 100000) (5317882685249 / 100000) := by
  exact
    packedTile8192 53170432 53186816 11 916 7291 26 _ _ (17789 / 1000) (1778903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53186816 :
    ThetaLowerSegment 53186816 53203200 (5317882685249 / 100000) (2659723182799 / 50000) := by
  exact
    packedTile8192 53186816 53203200 11 879 7292 26 _ _ (1778931 / 100000) (889467 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53203200 :
    ThetaLowerSegment 53203200 53219584 (2659723182799 / 50000) (5321116809977 / 100000) := by
  exact
    packedTile8192 53203200 53219584 11 939 7294 26 _ _ (1778961 / 100000) (444741 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53219584 :
    ThetaLowerSegment 53219584 53235968 (5321116809977 / 100000) (1064552119717 / 20000) := by
  exact
    packedTile8192 53219584 53235968 11 924 7295 26 _ _ (111187 / 6250) (355799 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53235968 :
    ThetaLowerSegment 53235968 53252352 (1064552119717 / 20000) (5324404415837 / 100000) := by
  exact
    packedTile8192 53235968 53252352 11 924 7296 26 _ _ (1779023 / 100000) (889513 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53252352 :
    ThetaLowerSegment 53252352 53268736 (5324404415837 / 100000) (5326067831327 / 100000) := by
  exact
    packedTile8192 53252352 53268736 11 935 7297 26 _ _ (889527 / 50000) (1779057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53268736 :
    ThetaLowerSegment 53268736 53285120 (5326067831327 / 100000) (5327686798677 / 100000) := by
  exact
    packedTile8192 53268736 53285120 11 910 7298 26 _ _ (355817 / 20000) (111193 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53285120 :
    ThetaLowerSegment 53285120 53301504 (5327686798677 / 100000) (2664700043211 / 50000) := by
  exact
    packedTile8192 53285120 53301504 11 963 7299 26 _ _ (355823 / 20000) (889559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53301504 :
    ThetaLowerSegment 53301504 53317888 (2664700043211 / 50000) (1332762338691 / 25000) := by
  exact
    packedTile8192 53301504 53317888 11 927 7300 26 _ _ (889573 / 50000) (1779149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53317888 :
    ThetaLowerSegment 53317888 53334272 (1332762338691 / 25000) (5332645276533 / 100000) := by
  exact
    packedTile8192 53317888 53334272 11 897 7301 26 _ _ (1779177 / 100000) (88959 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53334272 :
    ThetaLowerSegment 53334272 53350656 (5332645276533 / 100000) (5334342640011 / 100000) := by
  exact
    packedTile8192 53334272 53350656 11 954 7303 26 _ _ (1779207 / 100000) (177921 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53350656 :
    ThetaLowerSegment 53350656 53367040 (5334342640011 / 100000) (5335963525829 / 100000) := by
  exact
    packedTile8192 53350656 53367040 11 911 7304 26 _ _ (889619 / 50000) (1779241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53367040 :
    ThetaLowerSegment 53367040 53383424 (5335963525829 / 100000) (2668761972371 / 50000) := by
  exact
    packedTile8192 53367040 53383424 11 877 7305 26 _ _ (1779269 / 100000) (222409 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53383424 :
    ThetaLowerSegment 53383424 53399808 (2668761972371 / 50000) (2669583119321 / 50000) := by
  exact
    packedTile8192 53383424 53399808 11 923 7306 26 _ _ (17793 / 1000) (1779303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53399808 :
    ThetaLowerSegment 53399808 53416192 (2669583119321 / 50000) (333799200517 / 6250) := by
  exact
    packedTile8192 53399808 53416192 11 911 7307 26 _ _ (177933 / 10000) (1779333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53416192 :
    ThetaLowerSegment 53416192 53432576 (333799200517 / 6250) (5342468704417 / 100000) := by
  exact
    packedTile8192 53416192 53432576 11 945 7308 26 _ _ (1779361 / 100000) (444841 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53432576 :
    ThetaLowerSegment 53432576 53448960 (5342468704417 / 100000) (5344070157217 / 100000) := by
  exact
    packedTile8192 53432576 53448960 11 900 7309 26 _ _ (55606 / 3125) (355879 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53448960 :
    ThetaLowerSegment 53448960 53465344 (5344070157217 / 100000) (1069133971519 / 20000) := by
  exact
    packedTile8192 53448960 53465344 11 899 7310 26 _ _ (889711 / 50000) (71177 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53465344 :
    ThetaLowerSegment 53465344 53481728 (1069133971519 / 20000) (33420501641 / 625) := by
  exact
    packedTile8192 53465344 53481728 11 905 7312 26 _ _ (1779453 / 100000) (55608 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53481728 :
    ThetaLowerSegment 53481728 53498112 (33420501641 / 625) (334307781611 / 6250) := by
  exact
    packedTile8192 53481728 53498112 11 924 7313 26 _ _ (444871 / 25000) (1779487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53498112 :
    ThetaLowerSegment 53498112 53514496 (334307781611 / 6250) (2675271042001 / 50000) := by
  exact
    packedTile8192 53498112 53514496 11 909 7314 26 _ _ (889757 / 50000) (1779517 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53514496 :
    ThetaLowerSegment 53514496 53530880 (2675271042001 / 50000) (669021963289 / 12500) := by
  exact
    packedTile8192 53514496 53530880 11 918 7315 26 _ _ (355909 / 20000) (444887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53530880 :
    ThetaLowerSegment 53530880 53547264 (669021963289 / 12500) (2676908237231 / 50000) := by
  exact
    packedTile8192 53530880 53547264 11 922 7316 26 _ _ (71183 / 4000) (889789 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53547264 :
    ThetaLowerSegment 53547264 53563648 (2676908237231 / 50000) (133885586467 / 2500) := by
  exact
    packedTile8192 53547264 53563648 11 903 7317 26 _ _ (889803 / 50000) (1779609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53563648 :
    ThetaLowerSegment 53563648 53580032 (133885586467 / 2500) (5357026911617 / 100000) := by
  exact
    packedTile8192 53563648 53580032 11 901 7318 26 _ _ (1779637 / 100000) (44491 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53580032 :
    ThetaLowerSegment 53580032 53596416 (5357026911617 / 100000) (214346852957 / 4000) := by
  exact
    packedTile8192 53580032 53596416 11 924 7319 26 _ _ (1779667 / 100000) (177967 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53596416 :
    ThetaLowerSegment 53596416 53612800 (214346852957 / 4000) (1072056390123 / 20000) := by
  exact
    packedTile8192 53596416 53612800 11 905 7320 26 _ _ (889849 / 50000) (1779701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53612800 :
    ThetaLowerSegment 53612800 53629184 (1072056390123 / 20000) (5361880146359 / 100000) := by
  exact
    packedTile8192 53612800 53629184 11 898 7322 26 _ _ (111233 / 6250) (1779731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53629184 :
    ThetaLowerSegment 53629184 53645568 (5361880146359 / 100000) (1340884275497 / 25000) := by
  exact
    packedTile8192 53629184 53645568 11 931 7323 26 _ _ (1779759 / 100000) (889881 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53645568 :
    ThetaLowerSegment 53645568 53661952 (1340884275497 / 25000) (5365236800483 / 100000) := by
  exact
    packedTile8192 53645568 53661952 11 955 7324 26 _ _ (1779789 / 100000) (111237 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53661952 :
    ThetaLowerSegment 53661952 53678336 (5365236800483 / 100000) (5366925849663 / 100000) := by
  exact
    packedTile8192 53661952 53678336 11 949 7325 26 _ _ (88991 / 5000) (1779823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53678336 :
    ThetaLowerSegment 53678336 53694720 (5366925849663 / 100000) (5368517036457 / 100000) := by
  exact
    packedTile8192 53678336 53694720 11 894 7326 26 _ _ (1779851 / 100000) (889927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53694720 :
    ThetaLowerSegment 53694720 53711104 (5368517036457 / 100000) (2685056794857 / 50000) := by
  exact
    packedTile8192 53694720 53711104 11 897 7327 26 _ _ (1779881 / 100000) (444971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53711104 :
    ThetaLowerSegment 53711104 53727488 (2685056794857 / 50000) (2685908482749 / 50000) := by
  exact
    packedTile8192 53711104 53727488 11 957 7328 26 _ _ (222489 / 12500) (355983 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53727488 :
    ThetaLowerSegment 53727488 53743872 (2685908482749 / 50000) (2686727256069 / 50000) := by
  exact
    packedTile8192 53727488 53743872 11 920 7329 26 _ _ (889971 / 50000) (355989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53743872 :
    ThetaLowerSegment 53743872 53760256 (2686727256069 / 50000) (5375079627487 / 100000) := by
  exact
    packedTile8192 53743872 53760256 11 913 7331 26 _ _ (1779973 / 100000) (222497 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53760256 :
    ThetaLowerSegment 53760256 53776640 (5375079627487 / 100000) (5376702990223 / 100000) := by
  exact
    packedTile8192 53760256 53776640 11 912 7332 26 _ _ (1780003 / 100000) (890003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53776640 :
    ThetaLowerSegment 53776640 53793024 (5376702990223 / 100000) (1344583820121 / 25000) := by
  exact
    packedTile8192 53776640 53793024 11 917 7333 26 _ _ (1780033 / 100000) (445009 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53793024 :
    ThetaLowerSegment 53793024 53809408 (1344583820121 / 25000) (1345000800113 / 25000) := by
  exact
    packedTile8192 53793024 53809408 11 937 7334 26 _ _ (55627 / 3125) (1780067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53809408 :
    ThetaLowerSegment 53809408 53825792 (1345000800113 / 25000) (1345399541169 / 25000) := by
  exact
    packedTile8192 53809408 53825792 11 896 7335 26 _ _ (890047 / 50000) (1780097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53825792 :
    ThetaLowerSegment 53825792 53842176 (1345399541169 / 25000) (5383191376551 / 100000) := by
  exact
    packedTile8192 53825792 53842176 11 895 7336 26 _ _ (14241 / 800) (55629 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53842176 :
    ThetaLowerSegment 53842176 53858560 (5383191376551 / 100000) (168276076863 / 3125) := by
  exact
    packedTile8192 53842176 53858560 11 923 7337 26 _ _ (356031 / 20000) (890079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53858560 :
    ThetaLowerSegment 53858560 53874944 (168276076863 / 3125) (2693224544159 / 50000) := by
  exact
    packedTile8192 53858560 53874944 11 907 7338 26 _ _ (890093 / 50000) (1780189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53874944 :
    ThetaLowerSegment 53874944 53891328 (2693224544159 / 50000) (107762877079 / 2000) := by
  exact
    packedTile8192 53874944 53891328 11 952 7339 26 _ _ (222527 / 12500) (1780219 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53891328 :
    ThetaLowerSegment 53891328 53907712 (107762877079 / 2000) (5389815505883 / 100000) := by
  exact
    packedTile8192 53891328 53907712 11 939 7341 26 _ _ (1780247 / 100000) (7121 / 400) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53907712 :
    ThetaLowerSegment 53907712 53924096 (5389815505883 / 100000) (2695729350777 / 50000) := by
  exact
    packedTile8192 53907712 53924096 11 923 7342 26 _ _ (1780277 / 100000) (44507 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53924096 :
    ThetaLowerSegment 53924096 53940480 (2695729350777 / 50000) (1078609703141 / 20000) := by
  exact
    packedTile8192 53924096 53940480 11 893 7343 26 _ _ (1780307 / 100000) (178031 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53940480 :
    ThetaLowerSegment 53940480 53956864 (1078609703141 / 20000) (5394729154777 / 100000) := by
  exact
    packedTile8192 53940480 53956864 11 944 7344 26 _ _ (890169 / 50000) (1780341 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53956864 :
    ThetaLowerSegment 53956864 53973248 (5394729154777 / 100000) (5396375995177 / 100000) := by
  exact
    packedTile8192 53956864 53973248 11 925 7345 26 _ _ (111273 / 6250) (1780371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53973248 :
    ThetaLowerSegment 53973248 53989632 (5396375995177 / 100000) (5398047788899 / 100000) := by
  exact
    packedTile8192 53973248 53989632 11 939 7346 26 _ _ (890199 / 50000) (1780401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell53989632 :
    ThetaLowerSegment 53989632 54006016 (5398047788899 / 100000) (2699834879859 / 50000) := by
  exact
    packedTile8192 53989632 54006016 11 911 7347 26 _ _ (1780429 / 100000) (111277 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54006016 :
    ThetaLowerSegment 54006016 54022400 (2699834879859 / 50000) (5401316684293 / 100000) := by
  exact
    packedTile8192 54006016 54022400 11 925 7348 26 _ _ (1780459 / 100000) (890231 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54022400 :
    ThetaLowerSegment 54022400 54038784 (5401316684293 / 100000) (675366448477 / 12500) := by
  exact
    packedTile8192 54022400 54038784 11 907 7349 26 _ _ (1780489 / 100000) (445123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54038784 :
    ThetaLowerSegment 54038784 54055168 (675366448477 / 12500) (675570763147 / 12500) := by
  exact
    packedTile8192 54038784 54055168 11 918 7351 26 _ _ (44513 / 2500) (1780523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54055168 :
    ThetaLowerSegment 54055168 54071552 (675570763147 / 12500) (2703092312563 / 50000) := by
  exact
    packedTile8192 54055168 54071552 11 909 7352 26 _ _ (35611 / 2000) (1780553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54071552 :
    ThetaLowerSegment 54071552 54087936 (2703092312563 / 50000) (2703924733713 / 50000) := by
  exact
    packedTile8192 54071552 54087936 11 935 7353 26 _ _ (89029 / 5000) (1780583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54087936 :
    ThetaLowerSegment 54087936 54104320 (2703924733713 / 50000) (5409492971379 / 100000) := by
  exact
    packedTile8192 54087936 54104320 11 923 7354 26 _ _ (1780611 / 100000) (890307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54104320 :
    ThetaLowerSegment 54104320 54120704 (5409492971379 / 100000) (5411134722381 / 100000) := by
  exact
    packedTile8192 54104320 54120704 11 922 7355 26 _ _ (1780641 / 100000) (445161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54120704 :
    ThetaLowerSegment 54120704 54137088 (5411134722381 / 100000) (2706392702199 / 50000) := by
  exact
    packedTile8192 54120704 54137088 11 927 7356 26 _ _ (1780671 / 100000) (890337 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54137088 :
    ThetaLowerSegment 54137088 54153472 (2706392702199 / 50000) (1353604577033 / 25000) := by
  exact
    packedTile8192 54137088 54153472 11 917 7357 26 _ _ (890351 / 50000) (356141 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54153472 :
    ThetaLowerSegment 54153472 54169856 (1353604577033 / 25000) (1354004351367 / 25000) := by
  exact
    packedTile8192 54153472 54169856 11 898 7358 26 _ _ (445183 / 25000) (356147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54169856 :
    ThetaLowerSegment 54169856 54186240 (1354004351367 / 25000) (677204737361 / 12500) := by
  exact
    packedTile8192 54169856 54186240 11 910 7360 26 _ _ (890381 / 50000) (356153 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54186240 :
    ThetaLowerSegment 54186240 54202624 (677204737361 / 12500) (677408192847 / 12500) := by
  exact
    packedTile8192 54186240 54202624 11 914 7361 26 _ _ (222599 / 12500) (356159 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54202624 :
    ThetaLowerSegment 54202624 54219008 (677408192847 / 12500) (2710420785123 / 50000) := by
  exact
    packedTile8192 54202624 54219008 11 885 7362 26 _ _ (890411 / 50000) (71233 / 4000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54219008 :
    ThetaLowerSegment 54219008 54235392 (2710420785123 / 50000) (169452164684 / 3125) := by
  exact
    packedTile8192 54219008 54235392 11 914 7363 26 _ _ (1780853 / 100000) (222607 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54235392 :
    ThetaLowerSegment 54235392 54251776 (169452164684 / 3125) (1356025139679 / 25000) := by
  exact
    packedTile8192 54235392 54251776 11 916 7364 26 _ _ (1780883 / 100000) (890443 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54251776 :
    ThetaLowerSegment 54251776 54268160 (1356025139679 / 25000) (2712889089381 / 50000) := by
  exact
    packedTile8192 54251776 54268160 11 942 7365 26 _ _ (1780913 / 100000) (445229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54268160 :
    ThetaLowerSegment 54268160 54284544 (2712889089381 / 50000) (2713694075617 / 50000) := by
  exact
    packedTile8192 54268160 54284544 11 904 7366 26 _ _ (1780943 / 100000) (890473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54284544 :
    ThetaLowerSegment 54284544 54300928 (2713694075617 / 50000) (678631224997 / 12500) := by
  exact
    packedTile8192 54284544 54300928 11 933 7367 26 _ _ (890487 / 50000) (1780977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54300928 :
    ThetaLowerSegment 54300928 54317312 (678631224997 / 12500) (6788329237 / 125) := by
  exact
    packedTile8192 54300928 54317312 11 906 7368 26 _ _ (445251 / 25000) (1781007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54317312 :
    ThetaLowerSegment 54317312 54333696 (6788329237 / 125) (543234646673 / 10000) := by
  exact
    packedTile8192 54317312 54333696 11 945 7370 26 _ _ (890517 / 50000) (1781037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54333696 :
    ThetaLowerSegment 54333696 54350080 (543234646673 / 10000) (2716989851209 / 50000) := by
  exact
    packedTile8192 54333696 54350080 11 917 7371 26 _ _ (222633 / 12500) (1781067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54350080 :
    ThetaLowerSegment 54350080 54366464 (2716989851209 / 50000) (543559693577 / 10000) := by
  exact
    packedTile8192 54350080 54366464 11 908 7372 26 _ _ (890547 / 50000) (1781097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54366464 :
    ThetaLowerSegment 54366464 54382848 (543559693577 / 10000) (2718593739751 / 50000) := by
  exact
    packedTile8192 54366464 54382848 11 893 7373 26 _ _ (445281 / 25000) (1781127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54382848 :
    ThetaLowerSegment 54382848 54399232 (2718593739751 / 50000) (169963372573 / 3125) := by
  exact
    packedTile8192 54382848 54399232 11 921 7374 26 _ _ (890577 / 50000) (1781157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54399232 :
    ThetaLowerSegment 54399232 54415616 (169963372573 / 3125) (5440400708691 / 100000) := by
  exact
    packedTile8192 54399232 54415616 11 883 7375 26 _ _ (356237 / 20000) (445297 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54415616 :
    ThetaLowerSegment 54415616 54432000 (5440400708691 / 100000) (5442064363501 / 100000) := by
  exact
    packedTile8192 54415616 54432000 11 934 7376 26 _ _ (356243 / 20000) (890609 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54432000 :
    ThetaLowerSegment 54432000 54448384 (5442064363501 / 100000) (5443710233881 / 100000) := by
  exact
    packedTile8192 54432000 54448384 11 924 7377 26 _ _ (356249 / 20000) (55664 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54448384 :
    ThetaLowerSegment 54448384 54464768 (5443710233881 / 100000) (5445316943931 / 100000) := by
  exact
    packedTile8192 54448384 54464768 11 902 7378 26 _ _ (71251 / 4000) (890639 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54464768 :
    ThetaLowerSegment 54464768 54481152 (5445316943931 / 100000) (340435290691 / 6250) := by
  exact
    packedTile8192 54464768 54481152 11 925 7380 26 _ _ (356261 / 20000) (445327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54481152 :
    ThetaLowerSegment 54481152 54497536 (340435290691 / 6250) (5448583884571 / 100000) := by
  exact
    packedTile8192 54481152 54497536 11 909 7381 26 _ _ (356267 / 20000) (890669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54497536 :
    ThetaLowerSegment 54497536 54513920 (5448583884571 / 100000) (2725114042233 / 50000) := by
  exact
    packedTile8192 54497536 54513920 11 923 7382 26 _ _ (356273 / 20000) (222671 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54513920 :
    ThetaLowerSegment 54513920 54530304 (2725114042233 / 50000) (5451900814371 / 100000) := by
  exact
    packedTile8192 54513920 54530304 11 939 7383 26 _ _ (356279 / 20000) (890699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54530304 :
    ThetaLowerSegment 54530304 54546688 (5451900814371 / 100000) (681691797637 / 12500) := by
  exact
    packedTile8192 54530304 54546688 11 917 7384 26 _ _ (71257 / 4000) (445357 / 25000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54546688 :
    ThetaLowerSegment 54546688 54563072 (681691797637 / 12500) (5455189352791 / 100000) := by
  exact
    packedTile8192 54546688 54563072 11 929 7385 26 _ _ (356291 / 20000) (890729 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54563072 :
    ThetaLowerSegment 54563072 54579456 (5455189352791 / 100000) (682099308847 / 12500) := by
  exact
    packedTile8192 54563072 54579456 11 901 7386 26 _ _ (356297 / 20000) (111343 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54579456 :
    ThetaLowerSegment 54579456 54595840 (682099308847 / 12500) (1364620836749 / 25000) := by
  exact
    packedTile8192 54579456 54595840 11 948 7387 26 _ _ (356303 / 20000) (890759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54595840 :
    ThetaLowerSegment 54595840 54612224 (1364620836749 / 25000) (5460099208311 / 100000) := by
  exact
    packedTile8192 54595840 54612224 11 907 7388 26 _ _ (356309 / 20000) (445387 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54612224 :
    ThetaLowerSegment 54612224 54628608 (5460099208311 / 100000) (1365450153109 / 25000) := by
  exact
    packedTile8192 54612224 54628608 11 955 7390 26 _ _ (71263 / 4000) (890789 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54628608 :
    ThetaLowerSegment 54628608 54644992 (1365450153109 / 25000) (5463466413111 / 100000) := by
  exact
    packedTile8192 54628608 54644992 11 935 7391 26 _ _ (356321 / 20000) (222701 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54644992 :
    ThetaLowerSegment 54644992 54661376 (5463466413111 / 100000) (5465123333661 / 100000) := by
  exact
    packedTile8192 54644992 54661376 11 930 7392 26 _ _ (356327 / 20000) (890819 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54661376 :
    ThetaLowerSegment 54661376 54677760 (5465123333661 / 100000) (2733371433573 / 50000) := by
  exact
    packedTile8192 54661376 54677760 11 909 7393 26 _ _ (356333 / 20000) (445417 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54677760 :
    ThetaLowerSegment 54677760 54694144 (2733371433573 / 50000) (2734173196323 / 50000) := by
  exact
    packedTile8192 54677760 54694144 11 900 7394 26 _ _ (356339 / 20000) (890849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54694144 :
    ThetaLowerSegment 54694144 54710528 (2734173196323 / 50000) (5469962417221 / 100000) := by
  exact
    packedTile8192 54694144 54710528 11 907 7395 26 _ _ (71269 / 4000) (55679 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54710528 :
    ThetaLowerSegment 54710528 54726912 (5469962417221 / 100000) (341974322471 / 6250) := by
  exact
    packedTile8192 54710528 54726912 11 913 7396 26 _ _ (356351 / 20000) (890879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54726912 :
    ThetaLowerSegment 54726912 54743296 (341974322471 / 6250) (1368305318649 / 25000) := by
  exact
    packedTile8192 54726912 54743296 11 916 7397 26 _ _ (356357 / 20000) (445447 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54743296 :
    ThetaLowerSegment 54743296 54759680 (1368305318649 / 25000) (171088278378 / 3125) := by
  exact
    packedTile8192 54743296 54759680 11 900 7398 26 _ _ (356363 / 20000) (890909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54759680 :
    ThetaLowerSegment 54759680 54776064 (171088278378 / 3125) (5476501624241 / 100000) := by
  exact
    packedTile8192 54759680 54776064 11 941 7399 26 _ _ (356369 / 20000) (222731 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54776064 :
    ThetaLowerSegment 54776064 54792448 (5476501624241 / 100000) (5478123130491 / 100000) := by
  exact
    packedTile8192 54776064 54792448 11 910 7401 26 _ _ (2851 / 160) (890939 / 50000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54792448 :
    ThetaLowerSegment 54792448 54808832 (5478123130491 / 100000) (2739891042023 / 50000) := by
  exact
    packedTile8192 54792448 54808832 11 931 7402 26 _ _ (356381 / 20000) (445477 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54808832 :
    ThetaLowerSegment 54808832 54825216 (2739891042023 / 50000) (2740696476643 / 50000) := by
  exact
    packedTile8192 54808832 54825216 11 904 7403 26 _ _ (356387 / 20000) (890969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54825216 :
    ThetaLowerSegment 54825216 54841600 (2740696476643 / 50000) (342688854331 / 6250) := by
  exact
    packedTile8192 54825216 54841600 11 914 7404 26 _ _ (356393 / 20000) (111373 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54841600 :
    ThetaLowerSegment 54841600 54857984 (342688854331 / 6250) (2742318968927 / 50000) := by
  exact
    packedTile8192 54841600 54857984 11 907 7405 26 _ _ (890997 / 50000) (1781997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54857984 :
    ThetaLowerSegment 54857984 54874368 (2742318968927 / 50000) (548623997743 / 10000) := by
  exact
    packedTile8192 54857984 54874368 11 899 7406 26 _ _ (222753 / 12500) (1782027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54874368 :
    ThetaLowerSegment 54874368 54890752 (548623997743 / 10000) (685976691389 / 12500) := by
  exact
    packedTile8192 54874368 54890752 11 883 7407 26 _ _ (891027 / 50000) (1782057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54890752 :
    ThetaLowerSegment 54890752 54907136 (685976691389 / 12500) (686178066881 / 12500) := by
  exact
    packedTile8192 54890752 54907136 11 904 7408 26 _ _ (445521 / 25000) (1782087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54907136 :
    ThetaLowerSegment 54907136 54923520 (686178066881 / 12500) (2745540059477 / 50000) := by
  exact
    packedTile8192 54907136 54923520 11 929 7409 26 _ _ (891057 / 50000) (1782117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54923520 :
    ThetaLowerSegment 54923520 54939904 (2745540059477 / 50000) (2746343806421 / 50000) := by
  exact
    packedTile8192 54923520 54939904 11 902 7411 26 _ _ (55692 / 3125) (1782147 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54939904 :
    ThetaLowerSegment 54939904 54956288 (2746343806421 / 50000) (2747211725159 / 50000) := by
  exact
    packedTile8192 54939904 54956288 11 974 7412 26 _ _ (891087 / 50000) (1782177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54956288 :
    ThetaLowerSegment 54956288 54972672 (2747211725159 / 50000) (5496050601657 / 100000) := by
  exact
    packedTile8192 54956288 54972672 11 913 7413 26 _ _ (1782203 / 100000) (891103 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54972672 :
    ThetaLowerSegment 54972672 54989056 (5496050601657 / 100000) (2748860276989 / 50000) := by
  exact
    packedTile8192 54972672 54989056 11 937 7414 26 _ _ (1782233 / 100000) (445559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell54989056 :
    ThetaLowerSegment 54989056 55005440 (2748860276989 / 50000) (1374839167853 / 25000) := by
  exact
    packedTile8192 54989056 55005440 11 918 7415 26 _ _ (1782263 / 100000) (891133 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55005440 :
    ThetaLowerSegment 55005440 55021824 (1374839167853 / 25000) (2750507101951 / 50000) := by
  exact
    packedTile8192 55005440 55021824 11 930 7416 26 _ _ (1782293 / 100000) (222787 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55021824 :
    ThetaLowerSegment 55021824 55038208 (2750507101951 / 50000) (343917430849 / 6250) := by
  exact
    packedTile8192 55021824 55038208 11 934 7417 26 _ _ (1782323 / 100000) (891163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55038208 :
    ThetaLowerSegment 55038208 55054592 (343917430849 / 6250) (344020584471 / 6250) := by
  exact
    packedTile8192 55038208 55054592 11 926 7418 26 _ _ (111397 / 6250) (356471 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55054592 :
    ThetaLowerSegment 55054592 55070976 (344020584471 / 6250) (688250598827 / 12500) := by
  exact
    packedTile8192 55054592 55070976 11 940 7419 26 _ _ (891191 / 50000) (356477 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55070976 :
    ThetaLowerSegment 55070976 55087360 (688250598827 / 12500) (172114228254 / 3125) := by
  exact
    packedTile8192 55070976 55087360 11 926 7420 26 _ _ (445603 / 25000) (356483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55087360 :
    ThetaLowerSegment 55087360 55103744 (172114228254 / 3125) (2754669855909 / 50000) := by
  exact
    packedTile8192 55087360 55103744 11 945 7422 26 _ _ (891221 / 50000) (356489 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55103744 :
    ThetaLowerSegment 55103744 55120128 (2754669855909 / 50000) (110218593519 / 2000) := by
  exact
    packedTile8192 55103744 55120128 11 892 7423 26 _ _ (1782471 / 100000) (891237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55120128 :
    ThetaLowerSegment 55120128 55136512 (110218593519 / 2000) (8820125583 / 160) := by
  exact
    packedTile8192 55120128 55136512 11 925 7424 26 _ _ (1782501 / 100000) (222813 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55136512 :
    ThetaLowerSegment 55136512 55152896 (8820125583 / 160) (5514204157647 / 100000) := by
  exact
    packedTile8192 55136512 55152896 11 912 7425 26 _ _ (1782531 / 100000) (891267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55152896 :
    ThetaLowerSegment 55152896 55169280 (5514204157647 / 100000) (5515810244207 / 100000) := by
  exact
    packedTile8192 55152896 55169280 11 901 7426 26 _ _ (11141 / 625) (1782563 / 100000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55169280 :
    ThetaLowerSegment 55169280 55185664 (5515810244207 / 100000) (5517434183697 / 100000) := by
  exact
    packedTile8192 55169280 55185664 11 911 7427 26 _ _ (178259 / 10000) (1782593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55185664 :
    ThetaLowerSegment 55185664 55202048 (5517434183697 / 100000) (5519070628857 / 100000) := by
  exact
    packedTile8192 55185664 55202048 11 918 7428 26 _ _ (89131 / 5000) (1782623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55202048 :
    ThetaLowerSegment 55202048 55218432 (5519070628857 / 100000) (5520714232157 / 100000) := by
  exact
    packedTile8192 55202048 55218432 11 922 7429 26 _ _ (35653 / 2000) (1782653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55218432 :
    ThetaLowerSegment 55218432 55234816 (5520714232157 / 100000) (5522407777207 / 100000) := by
  exact
    packedTile8192 55218432 55234816 11 950 7430 26 _ _ (1782679 / 100000) (891341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55234816 :
    ThetaLowerSegment 55234816 55251200 (5522407777207 / 100000) (5524047869487 / 100000) := by
  exact
    packedTile8192 55234816 55251200 11 920 7432 26 _ _ (1782709 / 100000) (222839 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55251200 :
    ThetaLowerSegment 55251200 55267584 (5524047869487 / 100000) (276281457949 / 5000) := by
  exact
    packedTile8192 55251200 55267584 11 887 7433 26 _ _ (1782739 / 100000) (891371 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55267584 :
    ThetaLowerSegment 55267584 55283968 (276281457949 / 5000) (55272603917 / 1000) := by
  exact
    packedTile8192 55267584 55283968 11 915 7434 26 _ _ (111423 / 6250) (1782771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55283968 :
    ThetaLowerSegment 55283968 55300352 (55272603917 / 1000) (1382210879081 / 25000) := by
  exact
    packedTile8192 55283968 55300352 11 888 7435 26 _ _ (891399 / 50000) (1782801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55300352 :
    ThetaLowerSegment 55300352 55316736 (1382210879081 / 25000) (5530535419147 / 100000) := by
  exact
    packedTile8192 55300352 55316736 11 949 7436 26 _ _ (1782827 / 100000) (178283 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55316736 :
    ThetaLowerSegment 55316736 55333120 (5530535419147 / 100000) (2766097629507 / 50000) := by
  exact
    packedTile8192 55316736 55333120 11 931 7437 26 _ _ (1782857 / 100000) (89143 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55333120 :
    ThetaLowerSegment 55333120 55349504 (2766097629507 / 50000) (276689814577 / 5000) := by
  exact
    packedTile8192 55333120 55349504 11 898 7438 26 _ _ (1782887 / 100000) (178289 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55349504 :
    ThetaLowerSegment 55349504 55365888 (276689814577 / 5000) (1383856469191 / 25000) := by
  exact
    packedTile8192 55349504 55365888 11 914 7439 26 _ _ (445729 / 25000) (1782919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55365888 :
    ThetaLowerSegment 55365888 55382272 (1383856469191 / 25000) (2768537550907 / 50000) := by
  exact
    packedTile8192 55365888 55382272 11 925 7440 26 _ _ (891473 / 50000) (1782949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55382272 :
    ThetaLowerSegment 55382272 55398656 (2768537550907 / 50000) (2769371092187 / 50000) := by
  exact
    packedTile8192 55382272 55398656 11 935 7441 26 _ _ (55718 / 3125) (1782979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55398656 :
    ThetaLowerSegment 55398656 55415040 (2769371092187 / 50000) (1385087613721 / 25000) := by
  exact
    packedTile8192 55398656 55415040 11 902 7443 26 _ _ (356601 / 20000) (55719 / 3125) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55415040 :
    ThetaLowerSegment 55415040 55431424 (1385087613721 / 25000) (5542031856889 / 100000) := by
  exact
    packedTile8192 55415040 55431424 11 943 7444 26 _ _ (356607 / 20000) (891519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55431424 :
    ThetaLowerSegment 55431424 55447808 (5542031856889 / 100000) (1108734098541 / 20000) := by
  exact
    packedTile8192 55431424 55447808 11 919 7445 26 _ _ (222883 / 12500) (1783067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55447808 :
    ThetaLowerSegment 55447808 55464192 (1108734098541 / 20000) (5545285975869 / 100000) := by
  exact
    packedTile8192 55447808 55464192 11 906 7446 26 _ _ (891547 / 50000) (1783097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55464192 :
    ThetaLowerSegment 55464192 55480576 (5545285975869 / 100000) (2773462332953 / 50000) := by
  exact
    packedTile8192 55464192 55480576 11 919 7447 26 _ _ (1783123 / 100000) (891563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55480576 :
    ThetaLowerSegment 55480576 55496960 (2773462332953 / 50000) (5548577648737 / 100000) := by
  exact
    packedTile8192 55480576 55496960 11 927 7448 26 _ _ (1783153 / 100000) (445789 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55496960 :
    ThetaLowerSegment 55496960 55513344 (5548577648737 / 100000) (5550173596627 / 100000) := by
  exact
    packedTile8192 55496960 55513344 11 895 7449 26 _ _ (891591 / 50000) (356637 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55513344 :
    ThetaLowerSegment 55513344 55529728 (5550173596627 / 100000) (5551744606399 / 100000) := by
  exact
    packedTile8192 55513344 55529728 11 881 7450 26 _ _ (445803 / 25000) (356643 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55529728 :
    ThetaLowerSegment 55529728 55546112 (5551744606399 / 100000) (1388352092563 / 25000) := by
  exact
    packedTile8192 55529728 55546112 11 933 7451 26 _ _ (1783241 / 100000) (445811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55546112 :
    ThetaLowerSegment 55546112 55562496 (1388352092563 / 25000) (2777494174179 / 50000) := by
  exact
    packedTile8192 55546112 55562496 11 886 7452 26 _ _ (1783271 / 100000) (891637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55562496 :
    ThetaLowerSegment 55562496 55578880 (2777494174179 / 50000) (2778353724779 / 50000) := by
  exact
    packedTile8192 55562496 55578880 11 964 7454 26 _ _ (17833 / 1000) (1783303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55578880 :
    ThetaLowerSegment 55578880 55595264 (2778353724779 / 50000) (694788387071 / 12500) := by
  exact
    packedTile8192 55578880 55595264 11 897 7455 26 _ _ (178333 / 10000) (1783333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55595264 :
    ThetaLowerSegment 55595264 55611648 (694788387071 / 12500) (1111994194103 / 20000) := by
  exact
    packedTile8192 55595264 55611648 11 933 7456 26 _ _ (1783359 / 100000) (891681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55611648 :
    ThetaLowerSegment 55611648 55628032 (1111994194103 / 20000) (2780804952503 / 50000) := by
  exact
    packedTile8192 55611648 55628032 11 919 7457 26 _ _ (1783389 / 100000) (55731 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55628032 :
    ThetaLowerSegment 55628032 55644416 (2780804952503 / 50000) (1390812216537 / 25000) := by
  exact
    packedTile8192 55628032 55644416 11 919 7458 26 _ _ (891709 / 50000) (1783421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55644416 :
    ThetaLowerSegment 55644416 55660800 (1390812216537 / 25000) (1391222855439 / 25000) := by
  exact
    packedTile8192 55644416 55660800 11 921 7459 26 _ _ (222931 / 12500) (1783451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55660800 :
    ThetaLowerSegment 55660800 55677184 (1391222855439 / 25000) (5566569673613 / 100000) := by
  exact
    packedTile8192 55660800 55677184 11 941 7460 26 _ _ (1783477 / 100000) (44587 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55677184 :
    ThetaLowerSegment 55677184 55693568 (5566569673613 / 100000) (5568206933039 / 100000) := by
  exact
    packedTile8192 55677184 55693568 11 918 7461 26 _ _ (1783507 / 100000) (178351 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55693568 :
    ThetaLowerSegment 55693568 55709952 (5568206933039 / 100000) (1113975264547 / 20000) := by
  exact
    packedTile8192 55693568 55709952 11 936 7462 26 _ _ (111471 / 6250) (1783539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55709952 :
    ThetaLowerSegment 55709952 55726336 (1113975264547 / 20000) (278575235879 / 5000) := by
  exact
    packedTile8192 55709952 55726336 11 913 7463 26 _ _ (356713 / 20000) (111473 / 6250) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55726336 :
    ThetaLowerSegment 55726336 55742720 (278575235879 / 5000) (278659421563 / 5000) := by
  exact
    packedTile8192 55726336 55742720 11 944 7465 26 _ _ (356719 / 20000) (891799 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55742720 :
    ThetaLowerSegment 55742720 55759104 (278659421563 / 5000) (1393712246301 / 25000) := by
  exact
    packedTile8192 55742720 55759104 11 931 7466 26 _ _ (222953 / 12500) (1783627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55759104 :
    ThetaLowerSegment 55759104 55775488 (1393712246301 / 25000) (1394134972299 / 25000) := by
  exact
    packedTile8192 55759104 55775488 11 948 7467 26 _ _ (891827 / 50000) (1783657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55775488 :
    ThetaLowerSegment 55775488 55791872 (1394134972299 / 25000) (2789060116167 / 50000) := by
  exact
    packedTile8192 55775488 55791872 11 886 7468 26 _ _ (1783683 / 100000) (891843 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55791872 :
    ThetaLowerSegment 55791872 55808256 (2789060116167 / 50000) (2789877948119 / 50000) := by
  exact
    packedTile8192 55791872 55808256 11 917 7469 26 _ _ (55741 / 3125) (356743 / 20000) (by decide)
      (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55808256 :
    ThetaLowerSegment 55808256 55824640 (2789877948119 / 50000) (1395353248139 / 25000) := by
  exact
    packedTile8192 55808256 55824640 11 929 7470 26 _ _ (891871 / 50000) (356749 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55824640 :
    ThetaLowerSegment 55824640 55832832 (1395353248139 / 25000) (558222282459 / 10000) := by
  exact
    packedTile8192 55824640 55832832 10 454 7471 26 _ _ (1783771 / 100000) (891887 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell55832832 :
    ThetaLowerSegment 55832832 55836928 (558222282459 / 10000) (2791312980113 / 50000) := by
  exact
    packedTile8192 55832832 55836928 9 226 7472 26 _ _ (891893 / 50000) (1783789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_42488064_55836928 :
    ThetaLowerSegment 42488064 55836928 (4248067478303 / 100000) (2791312980113 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42488064 cell42504448)
                      (ThetaLowerSegment.join cell42520832 cell42537216))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42553600 cell42569984)
                      (ThetaLowerSegment.join cell42586368 cell42602752)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42619136 cell42635520)
                      (ThetaLowerSegment.join cell42651904 cell42668288))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42684672 cell42701056)
                      (ThetaLowerSegment.join cell42717440 cell42733824))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42750208 cell42766592)
                      (ThetaLowerSegment.join cell42782976 cell42799360))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42815744 cell42832128)
                      (ThetaLowerSegment.join cell42848512 cell42864896)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42881280 cell42897664)
                      (ThetaLowerSegment.join cell42914048 cell42930432))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell42946816 cell42963200)
                      (ThetaLowerSegment.join cell42979584 cell42995968)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43012352 cell43028736)
                      (ThetaLowerSegment.join cell43045120 cell43061504))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43077888 cell43094272)
                      (ThetaLowerSegment.join cell43110656 cell43127040)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43143424 cell43159808)
                      (ThetaLowerSegment.join cell43176192 cell43192576))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43208960 cell43225344)
                      (ThetaLowerSegment.join cell43241728 cell43258112))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43274496 cell43290880)
                      (ThetaLowerSegment.join cell43307264 cell43323648))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43340032 cell43356416)
                      (ThetaLowerSegment.join cell43372800 cell43389184)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43405568 cell43421952)
                      (ThetaLowerSegment.join cell43438336 cell43454720))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43471104 cell43487488)
                      (ThetaLowerSegment.join cell43503872 cell43520256))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43536640 cell43553024)
                      (ThetaLowerSegment.join cell43569408 cell43585792))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43602176 cell43618560)
                      (ThetaLowerSegment.join cell43634944 cell43651328)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43667712 cell43684096)
                      (ThetaLowerSegment.join cell43700480 cell43716864))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43733248 cell43749632)
                      (ThetaLowerSegment.join cell43766016 cell43782400))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43798784 cell43815168)
                      (ThetaLowerSegment.join cell43831552 cell43847936))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43864320 cell43880704)
                      (ThetaLowerSegment.join cell43897088 cell43913472)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43929856 cell43946240)
                      (ThetaLowerSegment.join cell43962624 cell43979008))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell43995392 cell44011776)
                      (ThetaLowerSegment.join cell44028160 cell44044544)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44060928 cell44077312)
                      (ThetaLowerSegment.join cell44093696 cell44110080))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44126464 cell44142848)
                      (ThetaLowerSegment.join cell44159232 cell44175616)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44192000 cell44208384)
                      (ThetaLowerSegment.join cell44224768 cell44241152))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44257536 cell44273920)
                      (ThetaLowerSegment.join cell44290304 cell44306688))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44323072 cell44339456)
                      (ThetaLowerSegment.join cell44355840 cell44372224))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44388608 cell44404992)
                      (ThetaLowerSegment.join cell44421376 cell44437760)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44454144 cell44470528)
                      (ThetaLowerSegment.join cell44486912 cell44503296))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44519680 cell44536064)
                      (ThetaLowerSegment.join cell44552448 cell44568832)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44585216 cell44601600)
                      (ThetaLowerSegment.join cell44617984 cell44634368))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44650752 cell44667136)
                      (ThetaLowerSegment.join cell44683520 cell44699904)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44716288 cell44732672)
                      (ThetaLowerSegment.join cell44749056 cell44765440))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44781824 cell44798208)
                      (ThetaLowerSegment.join cell44814592 cell44830976))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44847360 cell44863744)
                      (ThetaLowerSegment.join cell44880128 cell44896512))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44912896 cell44929280)
                      (ThetaLowerSegment.join cell44945664 cell44962048)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell44978432 cell44994816)
                      (ThetaLowerSegment.join cell45011200 cell45027584))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45043968 cell45060352)
                      (ThetaLowerSegment.join cell45076736 cell45093120)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45109504 cell45125888)
                      (ThetaLowerSegment.join cell45142272 cell45158656))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45175040 cell45191424)
                      (ThetaLowerSegment.join cell45207808 cell45224192)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45240576 cell45256960)
                      (ThetaLowerSegment.join cell45273344 cell45289728))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45306112 cell45322496)
                      (ThetaLowerSegment.join cell45338880 cell45355264))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45371648 cell45388032)
                      (ThetaLowerSegment.join cell45404416 cell45420800))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45437184 cell45453568)
                      (ThetaLowerSegment.join cell45469952 cell45486336)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45502720 cell45519104)
                      (ThetaLowerSegment.join cell45535488 cell45551872))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45568256 cell45584640)
                      (ThetaLowerSegment.join cell45601024 cell45617408))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45633792 cell45650176)
                      (ThetaLowerSegment.join cell45666560 cell45682944))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45699328 cell45715712)
                      (ThetaLowerSegment.join cell45732096 cell45748480)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45764864 cell45781248)
                      (ThetaLowerSegment.join cell45797632 cell45814016))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45830400 cell45846784)
                      (ThetaLowerSegment.join cell45863168 cell45879552))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45895936 cell45912320)
                      (ThetaLowerSegment.join cell45928704 cell45945088))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell45961472 cell45977856)
                      (ThetaLowerSegment.join cell45994240 cell46010624)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46027008 cell46043392)
                      (ThetaLowerSegment.join cell46059776 cell46076160))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46092544 cell46108928)
                      (ThetaLowerSegment.join cell46125312 cell46141696)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46158080 cell46174464)
                      (ThetaLowerSegment.join cell46190848 cell46207232))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46223616 cell46240000)
                      (ThetaLowerSegment.join cell46256384 cell46272768)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46289152 cell46305536)
                      (ThetaLowerSegment.join cell46321920 cell46338304))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46354688 cell46371072)
                      (ThetaLowerSegment.join cell46387456 cell46403840))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46420224 cell46436608)
                      (ThetaLowerSegment.join cell46452992 cell46469376))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46485760 cell46502144)
                      (ThetaLowerSegment.join cell46518528 cell46534912)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46551296 cell46567680)
                      (ThetaLowerSegment.join cell46584064 cell46600448))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46616832 cell46633216)
                      (ThetaLowerSegment.join cell46649600 cell46665984))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46682368 cell46698752)
                      (ThetaLowerSegment.join cell46715136 cell46731520))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46747904 cell46764288)
                      (ThetaLowerSegment.join cell46780672 cell46797056)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46813440 cell46829824)
                      (ThetaLowerSegment.join cell46846208 cell46862592))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46878976 cell46895360)
                      (ThetaLowerSegment.join cell46911744 cell46928128))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell46944512 cell46960896)
                      (ThetaLowerSegment.join cell46977280 cell46993664))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47010048 cell47026432)
                      (ThetaLowerSegment.join cell47042816 cell47059200)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47075584 cell47091968)
                      (ThetaLowerSegment.join cell47108352 cell47124736))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47141120 cell47157504)
                      (ThetaLowerSegment.join cell47173888 cell47190272)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47206656 cell47223040)
                      (ThetaLowerSegment.join cell47239424 cell47255808))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47272192 cell47288576)
                      (ThetaLowerSegment.join cell47304960 cell47321344)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47337728 cell47354112)
                      (ThetaLowerSegment.join cell47370496 cell47386880))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47403264 cell47419648)
                      (ThetaLowerSegment.join cell47436032 cell47452416))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47468800 cell47485184)
                      (ThetaLowerSegment.join cell47501568 cell47517952))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47534336 cell47550720)
                      (ThetaLowerSegment.join cell47567104 cell47583488)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47599872 cell47616256)
                      (ThetaLowerSegment.join cell47632640 cell47649024))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47665408 cell47681792)
                      (ThetaLowerSegment.join cell47698176 cell47714560))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47730944 cell47747328)
                      (ThetaLowerSegment.join cell47763712 cell47780096))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47796480 cell47812864)
                      (ThetaLowerSegment.join cell47829248 cell47845632)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47862016 cell47878400)
                      (ThetaLowerSegment.join cell47894784 cell47911168))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47927552 cell47943936)
                      (ThetaLowerSegment.join cell47960320 cell47976704))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell47993088 cell48009472)
                      (ThetaLowerSegment.join cell48025856 cell48042240))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48058624 cell48075008)
                      (ThetaLowerSegment.join cell48091392 cell48107776)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48124160 cell48140544)
                      (ThetaLowerSegment.join cell48156928 cell48173312))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48189696 cell48206080)
                      (ThetaLowerSegment.join cell48222464 cell48238848)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48255232 cell48271616)
                      (ThetaLowerSegment.join cell48288000 cell48304384))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48320768 cell48337152)
                      (ThetaLowerSegment.join cell48353536 cell48369920)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48386304 cell48402688)
                      (ThetaLowerSegment.join cell48419072 cell48435456))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48451840 cell48468224)
                      (ThetaLowerSegment.join cell48484608 cell48500992))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48517376 cell48533760)
                      (ThetaLowerSegment.join cell48550144 cell48566528))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48582912 cell48599296)
                      (ThetaLowerSegment.join cell48615680 cell48632064)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48648448 cell48664832)
                      (ThetaLowerSegment.join cell48681216 cell48697600))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48713984 cell48730368)
                      (ThetaLowerSegment.join cell48746752 cell48763136)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48779520 cell48795904)
                      (ThetaLowerSegment.join cell48812288 cell48828672))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48845056 cell48861440)
                      (ThetaLowerSegment.join cell48877824 cell48894208)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48910592 cell48926976)
                      (ThetaLowerSegment.join cell48943360 cell48959744))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell48976128 cell48992512)
                      (ThetaLowerSegment.join cell49008896 cell49025280))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49041664 cell49058048)
                      (ThetaLowerSegment.join cell49074432 cell49090816))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49107200 cell49123584)
                      (ThetaLowerSegment.join cell49139968 cell49156352)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49172736 cell49189120)
                      (ThetaLowerSegment.join cell49205504 cell49221888))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49238272 cell49254656)
                      (ThetaLowerSegment.join cell49271040 cell49287424)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49303808 cell49320192)
                      (ThetaLowerSegment.join cell49336576 cell49352960))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49369344 cell49385728)
                      (ThetaLowerSegment.join cell49402112 cell49418496)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49434880 cell49451264)
                      (ThetaLowerSegment.join cell49467648 cell49484032))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49500416 cell49516800)
                      (ThetaLowerSegment.join cell49533184 cell49549568))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49565952 cell49582336)
                      (ThetaLowerSegment.join cell49598720 cell49615104))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49631488 cell49647872)
                      (ThetaLowerSegment.join cell49664256 cell49680640)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49697024 cell49713408)
                      (ThetaLowerSegment.join cell49729792 cell49746176))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49762560 cell49778944)
                      (ThetaLowerSegment.join cell49795328 cell49811712))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49828096 cell49844480)
                      (ThetaLowerSegment.join cell49860864 cell49877248))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49893632 cell49910016)
                      (ThetaLowerSegment.join cell49926400 cell49942784)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell49959168 cell49975552)
                      (ThetaLowerSegment.join cell49991936 cell50008320))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50024704 cell50041088)
                      (ThetaLowerSegment.join cell50057472 cell50073856))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50090240 cell50106624)
                      (ThetaLowerSegment.join cell50123008 cell50139392))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50155776 cell50172160)
                      (ThetaLowerSegment.join cell50188544 cell50204928)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50221312 cell50237696)
                      (ThetaLowerSegment.join cell50254080 cell50270464))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50286848 cell50303232)
                      (ThetaLowerSegment.join cell50319616 cell50336000)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50352384 cell50368768)
                      (ThetaLowerSegment.join cell50385152 cell50401536))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50417920 cell50434304)
                      (ThetaLowerSegment.join cell50450688 cell50467072)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50483456 cell50499840)
                      (ThetaLowerSegment.join cell50516224 cell50532608))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50548992 cell50565376)
                      (ThetaLowerSegment.join cell50581760 cell50598144))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50614528 cell50630912)
                      (ThetaLowerSegment.join cell50647296 cell50663680))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50680064 cell50696448)
                      (ThetaLowerSegment.join cell50712832 cell50729216)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50745600 cell50761984)
                      (ThetaLowerSegment.join cell50778368 cell50794752))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50811136 cell50827520)
                      (ThetaLowerSegment.join cell50843904 cell50860288)))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50876672 cell50893056)
                      (ThetaLowerSegment.join cell50909440 cell50925824))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell50942208 cell50958592)
                      (ThetaLowerSegment.join cell50974976 cell50991360)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51007744 cell51024128)
                      (ThetaLowerSegment.join cell51040512 cell51056896))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51073280 cell51089664)
                      (ThetaLowerSegment.join cell51106048 cell51122432))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51138816 cell51155200)
                      (ThetaLowerSegment.join cell51171584 cell51187968))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51204352 cell51220736)
                      (ThetaLowerSegment.join cell51237120 cell51253504)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51269888 cell51286272)
                      (ThetaLowerSegment.join cell51302656 cell51319040))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51335424 cell51351808)
                      (ThetaLowerSegment.join cell51368192 cell51384576)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51400960 cell51417344)
                      (ThetaLowerSegment.join cell51433728 cell51450112))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51466496 cell51482880)
                      (ThetaLowerSegment.join cell51499264 cell51515648)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51532032 cell51548416)
                      (ThetaLowerSegment.join cell51564800 cell51581184))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51597568 cell51613952)
                      (ThetaLowerSegment.join cell51630336 cell51646720))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51663104 cell51679488)
                      (ThetaLowerSegment.join cell51695872 cell51712256))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51728640 cell51745024)
                      (ThetaLowerSegment.join cell51761408 cell51777792)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51794176 cell51810560)
                      (ThetaLowerSegment.join cell51826944 cell51843328))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51859712 cell51876096)
                      (ThetaLowerSegment.join cell51892480 cell51908864))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51925248 cell51941632)
                      (ThetaLowerSegment.join cell51958016 cell51974400))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell51990784 cell52007168)
                      (ThetaLowerSegment.join cell52023552 cell52039936)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52056320 cell52072704)
                      (ThetaLowerSegment.join cell52089088 cell52105472))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52121856 cell52138240)
                      (ThetaLowerSegment.join cell52154624 cell52171008))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52187392 cell52203776)
                      (ThetaLowerSegment.join cell52220160 cell52236544))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52252928 cell52269312)
                      (ThetaLowerSegment.join cell52285696 cell52302080)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52318464 cell52334848)
                      (ThetaLowerSegment.join cell52351232 cell52367616))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52384000 cell52400384)
                      (ThetaLowerSegment.join cell52416768 cell52433152)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52449536 cell52465920)
                      (ThetaLowerSegment.join cell52482304 cell52498688))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52515072 cell52531456)
                      (ThetaLowerSegment.join cell52547840 cell52564224)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52580608 cell52596992)
                      (ThetaLowerSegment.join cell52613376 cell52629760))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52646144 cell52662528)
                      (ThetaLowerSegment.join cell52678912 cell52695296))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52711680 cell52728064)
                      (ThetaLowerSegment.join cell52744448 cell52760832))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52777216 cell52793600)
                      (ThetaLowerSegment.join cell52809984 cell52826368)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52842752 cell52859136)
                      (ThetaLowerSegment.join cell52875520 cell52891904))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52908288 cell52924672)
                      (ThetaLowerSegment.join cell52941056 cell52957440)))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell52973824 cell52990208)
                      (ThetaLowerSegment.join cell53006592 cell53022976))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53039360 cell53055744)
                      (ThetaLowerSegment.join cell53072128 cell53088512)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53104896 cell53121280)
                      (ThetaLowerSegment.join cell53137664 cell53154048))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53170432 cell53186816)
                      (ThetaLowerSegment.join cell53203200 cell53219584))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53235968 cell53252352)
                      (ThetaLowerSegment.join cell53268736 cell53285120))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53301504 cell53317888)
                      (ThetaLowerSegment.join cell53334272 cell53350656)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53367040 cell53383424)
                      (ThetaLowerSegment.join cell53399808 cell53416192))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53432576 cell53448960)
                      (ThetaLowerSegment.join cell53465344 cell53481728)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53498112 cell53514496)
                      (ThetaLowerSegment.join cell53530880 cell53547264))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53563648 cell53580032)
                      (ThetaLowerSegment.join cell53596416 cell53612800)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53629184 cell53645568)
                      (ThetaLowerSegment.join cell53661952 cell53678336))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53694720 cell53711104)
                      (ThetaLowerSegment.join cell53727488 cell53743872))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53760256 cell53776640)
                      (ThetaLowerSegment.join cell53793024 cell53809408))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53825792 cell53842176)
                      (ThetaLowerSegment.join cell53858560 cell53874944)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53891328 cell53907712)
                      (ThetaLowerSegment.join cell53924096 cell53940480))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell53956864 cell53973248)
                      (ThetaLowerSegment.join cell53989632 cell54006016))))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54022400 cell54038784)
                      (ThetaLowerSegment.join cell54055168 cell54071552))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54087936 cell54104320)
                      (ThetaLowerSegment.join cell54120704 cell54137088)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54153472 cell54169856)
                      (ThetaLowerSegment.join cell54186240 cell54202624))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54219008 cell54235392)
                      (ThetaLowerSegment.join cell54251776 cell54268160))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54284544 cell54300928)
                      (ThetaLowerSegment.join cell54317312 cell54333696))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54350080 cell54366464)
                      (ThetaLowerSegment.join cell54382848 cell54399232)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54415616 cell54432000)
                      (ThetaLowerSegment.join cell54448384 cell54464768))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54481152 cell54497536)
                      (ThetaLowerSegment.join cell54513920 cell54530304)))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54546688 cell54563072)
                      (ThetaLowerSegment.join cell54579456 cell54595840))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54612224 cell54628608)
                      (ThetaLowerSegment.join cell54644992 cell54661376)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54677760 cell54694144)
                      (ThetaLowerSegment.join cell54710528 cell54726912))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54743296 cell54759680)
                      (ThetaLowerSegment.join cell54776064 cell54792448))))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54808832 cell54825216)
                      (ThetaLowerSegment.join cell54841600 cell54857984))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54874368 cell54890752)
                      (ThetaLowerSegment.join cell54907136 cell54923520)))
                  (ThetaLowerSegment.join
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell54939904 cell54956288)
                      (ThetaLowerSegment.join cell54972672 cell54989056))
                    (ThetaLowerSegment.join (ThetaLowerSegment.join cell55005440 cell55021824)
                      (ThetaLowerSegment.join cell55038208 cell55054592))))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55070976 cell55087360)
                  (ThetaLowerSegment.join cell55103744 cell55120128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55136512 cell55152896)
                  (ThetaLowerSegment.join cell55169280 cell55185664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55202048 cell55218432)
                  (ThetaLowerSegment.join cell55234816 cell55251200))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55267584 cell55283968)
                  (ThetaLowerSegment.join cell55300352 cell55316736))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55333120 cell55349504)
                  (ThetaLowerSegment.join cell55365888 cell55382272))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55398656 cell55415040)
                  (ThetaLowerSegment.join cell55431424 cell55447808)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55464192 cell55480576)
                  (ThetaLowerSegment.join cell55496960 cell55513344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell55529728 cell55546112)
                  (ThetaLowerSegment.join cell55562496 cell55578880)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell55595264 cell55611648)
                (ThetaLowerSegment.join cell55628032 cell55644416))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell55660800 cell55677184)
                (ThetaLowerSegment.join cell55693568 cell55709952)))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell55726336 cell55742720)
                (ThetaLowerSegment.join cell55759104 cell55775488))
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell55791872 cell55808256)
                (ThetaLowerSegment.join cell55824640 cell55832832)))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
