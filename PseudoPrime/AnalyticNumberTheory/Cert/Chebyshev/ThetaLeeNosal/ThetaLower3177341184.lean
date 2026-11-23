/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 3177341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell3145341184 :
    ThetaLowerSegment 3145341184 3145472256 (314525997612409 / 100000)
      (62907805452779 / 20000) := by
  exact
    packedTile65536 3145341184 3145472256 14 5958 56083 32 _ _ (2186917 / 100000) (54673 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145472256 :
    ThetaLowerSegment 3145472256 3145603328 (62907805452779 / 20000) (9829751437644 / 3125) := by
  exact
    packedTile65536 3145472256 3145603328 14 5953 56084 32 _ _ (2186921 / 100000) (546731 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145603328 :
    ThetaLowerSegment 3145603328 3145734400 (9829751437644 / 3125) (78641255805873 / 25000) := by
  exact
    packedTile65536 3145603328 3145734400 14 5934 56085 32 _ _ (1093463 / 50000) (2186929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145734400 :
    ThetaLowerSegment 3145734400 3145865472 (78641255805873 / 25000) (157289040691261 / 50000) := by
  exact
    packedTile65536 3145734400 3145865472 14 5971 56086 32 _ _ (218693 / 10000) (2186933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145865472 :
    ThetaLowerSegment 3145865472 3145996544 (157289040691261 / 50000) (78647833003907 / 25000) := by
  exact
    packedTile65536 3145865472 3145996544 14 6059 56088 32 _ _ (1093467 / 50000) (2186937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3145996544 :
    ThetaLowerSegment 3145996544 3146127616 (78647833003907 / 25000) (157302341636059 / 50000) := by
  exact
    packedTile65536 3145996544 3146127616 14 6105 56089 32 _ _ (1093469 / 50000) (2186941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146127616 :
    ThetaLowerSegment 3146127616 3146258688 (157302341636059 / 50000) (78654458338591 / 25000) := by
  exact
    packedTile65536 3146127616 3146258688 14 6013 56090 32 _ _ (1093471 / 50000) (437389 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146258688 :
    ThetaLowerSegment 3146258688 3146389760 (78654458338591 / 25000) (157315432682789 / 50000) := by
  exact
    packedTile65536 3146258688 3146389760 14 5959 56091 32 _ _ (1093473 / 50000) (2186949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146389760 :
    ThetaLowerSegment 3146389760 3146520832 (157315432682789 / 50000) (78660951935399 / 25000) := by
  exact
    packedTile65536 3146389760 3146520832 14 5918 56092 32 _ _ (2186951 / 100000) (1093477 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146520832 :
    ThetaLowerSegment 3146520832 3146651904 (78660951935399 / 25000)
      (314656927284641 / 100000) := by
  exact
    packedTile65536 3146520832 3146651904 14 5999 56093 32 _ _ (437391 / 20000) (1093479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146651904 :
    ThetaLowerSegment 3146651904 3146782976 (314656927284641 / 100000)
      (31466998561683 / 10000) := by
  exact
    packedTile65536 3146651904 3146782976 14 5971 56095 32 _ _ (2186959 / 100000) (1093481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146782976 :
    ThetaLowerSegment 3146782976 3146914048 (31466998561683 / 10000) (157341544949563 / 50000) := by
  exact
    packedTile65536 3146782976 3146914048 14 5992 56096 32 _ _ (2186963 / 100000) (1093483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3146914048 :
    ThetaLowerSegment 3146914048 3147045120 (157341544949563 / 50000) (31469610672671 / 10000) := by
  exact
    packedTile65536 3146914048 3147045120 14 5952 56097 32 _ _ (2186967 / 100000) (218697 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147045120 :
    ThetaLowerSegment 3147045120 3147176192 (31469610672671 / 10000) (157354618650297 / 50000) := by
  exact
    packedTile65536 3147045120 3147176192 14 6004 56098 32 _ _ (2186971 / 100000) (1093487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147176192 :
    ThetaLowerSegment 3147176192 3147307264 (157354618650297 / 50000)
      (157361238626649 / 50000) := by
  exact
    packedTile65536 3147176192 3147307264 14 6054 56099 32 _ _ (68343 / 3125) (2186979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147307264 :
    ThetaLowerSegment 3147307264 3147438336 (157361238626649 / 50000)
      (157367778790339 / 50000) := by
  exact
    packedTile65536 3147307264 3147438336 14 5981 56100 32 _ _ (109349 / 5000) (2186983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147438336 :
    ThetaLowerSegment 3147438336 3147569408 (157367778790339 / 50000)
      (157374360518687 / 50000) := by
  exact
    packedTile65536 3147438336 3147569408 14 6019 56102 32 _ _ (273373 / 12500) (2186987 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147569408 :
    ThetaLowerSegment 3147569408 3147700480 (157374360518687 / 50000)
      (157380952100519 / 50000) := by
  exact
    packedTile65536 3147569408 3147700480 14 6028 56103 32 _ _ (546747 / 25000) (2186991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147700480 :
    ThetaLowerSegment 3147700480 3147831552 (157380952100519 / 50000)
      (157387644296039 / 50000) := by
  exact
    packedTile65536 3147700480 3147831552 14 6120 56104 32 _ _ (136687 / 6250) (437399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147831552 :
    ThetaLowerSegment 3147831552 3147962624 (157387644296039 / 50000)
      (157394255584947 / 50000) := by
  exact
    packedTile65536 3147831552 3147962624 14 6046 56105 32 _ _ (546749 / 25000) (2186999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3147962624 :
    ThetaLowerSegment 3147962624 3148093696 (157394255584947 / 50000)
      (314801665980909 / 100000) := by
  exact
    packedTile65536 3147962624 3148093696 14 6015 56106 32 _ _ (2187001 / 100000) (546751 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3148093696 :
    ThetaLowerSegment 3148093696 3148224768 (314801665980909 / 100000)
      (314814634920559 / 100000) := by
  exact
    packedTile65536 3148093696 3148224768 14 5930 56107 32 _ _ (437401 / 20000) (68344 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3148224768 :
    ThetaLowerSegment 3148224768 3148355840 (314814634920559 / 100000)
      (314827625754019 / 100000) := by
  exact
    packedTile65536 3148224768 3148355840 14 5940 56109 32 _ _ (2187009 / 100000) (546753 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3148355840 :
    ThetaLowerSegment 3148355840 3148486912 (314827625754019 / 100000)
      (78710198439823 / 25000) := by
  exact
    packedTile65536 3148355840 3148486912 14 6021 56110 32 _ _ (2187013 / 100000) (273377 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3148486912 :
    ThetaLowerSegment 3148486912 3148617984 (78710198439823 / 25000)
      (314853992406887 / 100000) := by
  exact
    packedTile65536 3148486912 3148617984 14 6035 56111 32 _ _ (2187017 / 100000) (109351 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3148617984 :
    ThetaLowerSegment 3148617984 3148749056 (314853992406887 / 100000)
      (157433481814219 / 50000) := by
  exact
    packedTile65536 3148617984 3148749056 14 5931 56112 32 _ _ (2187021 / 100000) (136689 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3148749056 :
    ThetaLowerSegment 3148749056 3148880128 (157433481814219 / 50000)
      (157440084445713 / 50000) := by
  exact
    packedTile65536 3148749056 3148880128 14 6038 56113 32 _ _ (1093513 / 50000) (2187029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3148880128 :
    ThetaLowerSegment 3148880128 3149011200 (157440084445713 / 50000)
      (157446663031953 / 50000) := by
  exact
    packedTile65536 3148880128 3149011200 14 6016 56114 32 _ _ (218703 / 10000) (2187033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149011200 :
    ThetaLowerSegment 3149011200 3149142272 (157446663031953 / 50000)
      (157453145400729 / 50000) := by
  exact
    packedTile65536 3149011200 3149142272 14 5928 56116 32 _ _ (1093517 / 50000) (2187037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149142272 :
    ThetaLowerSegment 3149142272 3149273344 (157453145400729 / 50000) (31491944364799 / 10000) := by
  exact
    packedTile65536 3149142272 3149273344 14 6014 56117 32 _ _ (1093519 / 50000) (2187041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149273344 :
    ThetaLowerSegment 3149273344 3149404416 (31491944364799 / 10000) (78733129993027 / 25000) := by
  exact
    packedTile65536 3149273344 3149404416 14 5979 56118 32 _ _ (1093521 / 50000) (437409 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149404416 :
    ThetaLowerSegment 3149404416 3149535488 (78733129993027 / 25000) (19684107834741 / 6250) := by
  exact
    packedTile65536 3149404416 3149535488 14 6038 56119 32 _ _ (1093523 / 50000) (2187049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149535488 :
    ThetaLowerSegment 3149535488 3149666560 (19684107834741 / 6250) (157479369154653 / 50000) := by
  exact
    packedTile65536 3149535488 3149666560 14 5950 56120 32 _ _ (2187051 / 100000) (1093527 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149666560 :
    ThetaLowerSegment 3149666560 3149797632 (157479369154653 / 50000) (39371456882017 / 12500) := by
  exact
    packedTile65536 3149666560 3149797632 14 5906 56121 32 _ _ (437411 / 20000) (1093529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149797632 :
    ThetaLowerSegment 3149797632 3149928704 (39371456882017 / 12500) (78746244654891 / 25000) := by
  exact
    packedTile65536 3149797632 3149928704 14 6092 56123 32 _ _ (2187059 / 100000) (1093531 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3149928704 :
    ThetaLowerSegment 3149928704 3150059776 (78746244654891 / 25000)
      (314997998205603 / 100000) := by
  exact
    packedTile65536 3149928704 3150059776 14 5953 56124 32 _ _ (2187063 / 100000) (1093533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150059776 :
    ThetaLowerSegment 3150059776 3150190848 (314997998205603 / 100000)
      (157505504533593 / 50000) := by
  exact
    packedTile65536 3150059776 3150190848 14 5949 56125 32 _ _ (2187067 / 100000) (218707 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150190848 :
    ThetaLowerSegment 3150190848 3150321920 (157505504533593 / 50000) (39378019170487 / 12500) := by
  exact
    packedTile65536 3150190848 3150321920 14 6010 56126 32 _ _ (2187071 / 100000) (1093537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150321920 :
    ThetaLowerSegment 3150321920 3150452992 (39378019170487 / 12500) (78759239673469 / 25000) := by
  exact
    packedTile65536 3150321920 3150452992 14 5855 56127 32 _ _ (546769 / 25000) (2187079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150452992 :
    ThetaLowerSegment 3150452992 3150584064 (78759239673469 / 25000) (78762564581839 / 25000) := by
  exact
    packedTile65536 3150452992 3150584064 14 6081 56128 32 _ _ (54677 / 2500) (2187083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150584064 :
    ThetaLowerSegment 3150584064 3150715136 (78762564581839 / 25000) (78765888949519 / 25000) := by
  exact
    packedTile65536 3150584064 3150715136 14 6080 56130 32 _ _ (546771 / 25000) (2187087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150715136 :
    ThetaLowerSegment 3150715136 3150846208 (78765888949519 / 25000) (78769192545943 / 25000) := by
  exact
    packedTile65536 3150715136 3150846208 14 6042 56131 32 _ _ (136693 / 6250) (2187091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150846208 :
    ThetaLowerSegment 3150846208 3150977280 (78769192545943 / 25000) (39386254908867 / 12500) := by
  exact
    packedTile65536 3150846208 3150977280 14 6067 56132 32 _ _ (546773 / 25000) (437419 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3150977280 :
    ThetaLowerSegment 3150977280 3151108352 (39386254908867 / 12500) (19693949939223 / 6250) := by
  exact
    packedTile65536 3150977280 3151108352 14 6017 56133 32 _ _ (273387 / 12500) (2187099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3151108352 :
    ThetaLowerSegment 3151108352 3151239424 (19693949939223 / 6250) (39389524894489 / 12500) := by
  exact
    packedTile65536 3151108352 3151239424 14 5944 56134 32 _ _ (2187101 / 100000) (68347 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3151239424 :
    ThetaLowerSegment 3151239424 3151370496 (39389524894489 / 12500) (78782354504633 / 25000) := by
  exact
    packedTile65536 3151239424 3151370496 14 6044 56135 32 _ _ (437421 / 20000) (546777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3151370496 :
    ThetaLowerSegment 3151370496 3151501568 (78782354504633 / 25000)
      (315142586601821 / 100000) := by
  exact
    packedTile65536 3151370496 3151501568 14 6021 56137 32 _ _ (2187109 / 100000) (273389 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3151501568 :
    ThetaLowerSegment 3151501568 3151632640 (315142586601821 / 100000) (19697228959403 / 6250) := by
  exact
    packedTile65536 3151501568 3151632640 14 5979 56138 32 _ _ (2187113 / 100000) (546779 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3151632640 :
    ThetaLowerSegment 3151632640 3151763712 (19697228959403 / 6250) (31516875543281 / 10000) := by
  exact
    packedTile65536 3151632640 3151763712 14 5986 56139 32 _ _ (2187117 / 100000) (27339 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3151763712 :
    ThetaLowerSegment 3151763712 3151894784 (31516875543281 / 10000) (78795440013569 / 25000) := by
  exact
    packedTile65536 3151763712 3151894784 14 5946 56140 32 _ _ (2187121 / 100000) (546781 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3151894784 :
    ThetaLowerSegment 3151894784 3152025856 (78795440013569 / 25000)
      (315194915611151 / 100000) := by
  exact
    packedTile65536 3151894784 3152025856 14 6015 56141 32 _ _ (17497 / 800) (273391 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152025856 :
    ThetaLowerSegment 3152025856 3152156928 (315194915611151 / 100000)
      (315207869982141 / 100000) := by
  exact
    packedTile65536 3152025856 3152156928 14 5923 56142 32 _ _ (218713 / 10000) (2187133 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152156928 :
    ThetaLowerSegment 3152156928 3152288000 (315207869982141 / 100000)
      (315220977476203 / 100000) := by
  exact
    packedTile65536 3152156928 3152288000 14 5993 56144 32 _ _ (1093567 / 50000) (2187137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152288000 :
    ThetaLowerSegment 3152288000 3152419072 (315220977476203 / 100000)
      (315234148421239 / 100000) := by
  exact
    packedTile65536 3152288000 3152419072 14 6022 56145 32 _ _ (1093569 / 50000) (2187141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152419072 :
    ThetaLowerSegment 3152419072 3152550144 (315234148421239 / 100000)
      (315247290957517 / 100000) := by
  exact
    packedTile65536 3152419072 3152550144 14 6009 56146 32 _ _ (1093571 / 50000) (437429 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152550144 :
    ThetaLowerSegment 3152550144 3152681216 (315247290957517 / 100000)
      (315260512255087 / 100000) := by
  exact
    packedTile65536 3152550144 3152681216 14 6045 56147 32 _ _ (1093573 / 50000) (2187149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152681216 :
    ThetaLowerSegment 3152681216 3152812288 (315260512255087 / 100000)
      (315273716079637 / 100000) := by
  exact
    packedTile65536 3152681216 3152812288 14 6037 56148 32 _ _ (43743 / 2000) (2187153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152812288 :
    ThetaLowerSegment 3152812288 3152943360 (315273716079637 / 100000)
      (315286720903267 / 100000) := by
  exact
    packedTile65536 3152812288 3152943360 14 5946 56149 32 _ _ (437431 / 20000) (1093579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3152943360 :
    ThetaLowerSegment 3152943360 3153074432 (315286720903267 / 100000)
      (315299865728857 / 100000) := by
  exact
    packedTile65536 3152943360 3153074432 14 6010 56151 32 _ _ (2187159 / 100000) (1093581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153074432 :
    ThetaLowerSegment 3153074432 3153205504 (315299865728857 / 100000)
      (315312940589271 / 100000) := by
  exact
    packedTile65536 3153074432 3153205504 14 5978 56152 32 _ _ (2187163 / 100000) (1093583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153205504 :
    ThetaLowerSegment 3153205504 3153336576 (315312940589271 / 100000)
      (78831521912527 / 25000) := by
  exact
    packedTile65536 3153205504 3153336576 14 6011 56153 32 _ _ (2187167 / 100000) (218717 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153336576 :
    ThetaLowerSegment 3153336576 3153467648 (78831521912527 / 25000) (157669655642987 / 50000) := by
  exact
    packedTile65536 3153336576 3153467648 14 6046 56154 32 _ _ (2187171 / 100000) (1093587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153467648 :
    ThetaLowerSegment 3153467648 3153598720 (157669655642987 / 50000)
      (157676077188787 / 50000) := by
  exact
    packedTile65536 3153467648 3153598720 14 5872 56155 32 _ _ (87487 / 4000) (1093589 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153598720 :
    ThetaLowerSegment 3153598720 3153729792 (157676077188787 / 50000)
      (157682692314697 / 50000) := by
  exact
    packedTile65536 3153598720 3153729792 14 6049 56156 32 _ _ (109359 / 5000) (2187183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153729792 :
    ThetaLowerSegment 3153729792 3153860864 (157682692314697 / 50000) (1261513453517 / 400) := by
  exact
    packedTile65536 3153729792 3153860864 14 5934 56158 32 _ _ (136699 / 6250) (2187187 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153860864 :
    ThetaLowerSegment 3153860864 3153991936 (1261513453517 / 400) (157695773874257 / 50000) := by
  exact
    packedTile65536 3153860864 3153991936 14 6028 56159 32 _ _ (546797 / 25000) (2187191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3153991936 :
    ThetaLowerSegment 3153991936 3154123008 (157695773874257 / 50000) (31540483056553 / 10000) := by
  exact
    packedTile65536 3153991936 3154123008 14 6073 56160 32 _ _ (273399 / 12500) (437439 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3154123008 :
    ThetaLowerSegment 3154123008 3154254080 (31540483056553 / 10000) (157708915629277 / 50000) := by
  exact
    packedTile65536 3154123008 3154254080 14 5944 56161 32 _ _ (546799 / 25000) (2187199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3154254080 :
    ThetaLowerSegment 3154254080 3154385152 (157708915629277 / 50000)
      (157715563623677 / 50000) := by
  exact
    packedTile65536 3154254080 3154385152 14 6079 56162 32 _ _ (2734 / 125) (2187203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3154385152 :
    ThetaLowerSegment 3154385152 3154516224 (157715563623677 / 50000)
      (157722190851797 / 50000) := by
  exact
    packedTile65536 3154385152 3154516224 14 6060 56163 32 _ _ (546801 / 25000) (2187207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3154516224 :
    ThetaLowerSegment 3154516224 3154647296 (157722190851797 / 50000)
      (315457581509909 / 100000) := by
  exact
    packedTile65536 3154516224 3154647296 14 6035 56165 32 _ _ (2187209 / 100000) (546803 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3154647296 :
    ThetaLowerSegment 3154647296 3154778368 (315457581509909 / 100000)
      (157735265999041 / 50000) := by
  exact
    packedTile65536 3154647296 3154778368 14 5921 56166 32 _ _ (2187213 / 100000) (136701 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3154778368 :
    ThetaLowerSegment 3154778368 3154909440 (157735265999041 / 50000) (78870928041931 / 25000) := by
  exact
    packedTile65536 3154778368 3154909440 14 6026 56167 32 _ _ (2187217 / 100000) (109361 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3154909440 :
    ThetaLowerSegment 3154909440 3155040512 (78870928041931 / 25000)
      (315496894548691 / 100000) := by
  exact
    packedTile65536 3154909440 3155040512 14 6027 56168 32 _ _ (2187221 / 100000) (273403 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155040512 :
    ThetaLowerSegment 3155040512 3155171584 (315496894548691 / 100000) (19719357117151 / 6250) := by
  exact
    packedTile65536 3155040512 3155171584 14 5861 56169 32 _ _ (87489 / 4000) (546807 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155171584 :
    ThetaLowerSegment 3155171584 3155302656 (19719357117151 / 6250) (315523005665049 / 100000) := by
  exact
    packedTile65536 3155171584 3155302656 14 6077 56170 32 _ _ (2187229 / 100000) (68351 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155302656 :
    ThetaLowerSegment 3155302656 3155433728 (315523005665049 / 100000)
      (63107223189129 / 20000) := by
  exact
    packedTile65536 3155302656 3155433728 14 5994 56172 32 _ _ (1093617 / 50000) (2187237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155433728 :
    ThetaLowerSegment 3155433728 3155564800 (63107223189129 / 20000)
      (315549049083939 / 100000) := by
  exact
    packedTile65536 3155433728 3155564800 14 5913 56173 32 _ _ (1093619 / 50000) (2187241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155564800 :
    ThetaLowerSegment 3155564800 3155695872 (315549049083939 / 100000)
      (63112420508839 / 20000) := by
  exact
    packedTile65536 3155564800 3155695872 14 5968 56174 32 _ _ (1093621 / 50000) (437449 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155695872 :
    ThetaLowerSegment 3155695872 3155826944 (63112420508839 / 20000)
      (315575239143671 / 100000) := by
  exact
    packedTile65536 3155695872 3155826944 14 6006 56175 32 _ _ (1093623 / 50000) (2187249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155826944 :
    ThetaLowerSegment 3155826944 3155958016 (315575239143671 / 100000)
      (315588546372671 / 100000) := by
  exact
    packedTile65536 3155826944 3155958016 14 6084 56176 32 _ _ (8749 / 400) (2187253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3155958016 :
    ThetaLowerSegment 3155958016 3156089088 (315588546372671 / 100000)
      (315601481792827 / 100000) := by
  exact
    packedTile65536 3155958016 3156089088 14 5914 56177 32 _ _ (1093627 / 50000) (2187257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3156089088 :
    ThetaLowerSegment 3156089088 3156220160 (315601481792827 / 100000)
      (315614740950823 / 100000) := by
  exact
    packedTile65536 3156089088 3156220160 14 6062 56179 32 _ _ (1093629 / 50000) (2187261 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3156220160 :
    ThetaLowerSegment 3156220160 3156351232 (315614740950823 / 100000)
      (78906994019809 / 25000) := by
  exact
    packedTile65536 3156220160 3156351232 14 6051 56180 32 _ _ (2187263 / 100000) (1093633 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3156351232 :
    ThetaLowerSegment 3156351232 3156482304 (78906994019809 / 25000)
      (315640979381551 / 100000) := by
  exact
    packedTile65536 3156351232 3156482304 14 5945 56181 32 _ _ (2187267 / 100000) (218727 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3156482304 :
    ThetaLowerSegment 3156482304 3156613376 (315640979381551 / 100000)
      (63130874845831 / 20000) := by
  exact
    packedTile65536 3156482304 3156613376 14 6124 56182 32 _ _ (2187271 / 100000) (1093637 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3156613376 :
    ThetaLowerSegment 3156613376 3156744448 (63130874845831 / 20000) (63133485577271 / 20000) := by
  exact
    packedTile65536 3156613376 3156744448 14 5968 56183 32 _ _ (87491 / 4000) (1093639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3156744448 :
    ThetaLowerSegment 3156744448 3156875520 (63133485577271 / 20000) (63136088439281 / 20000) := by
  exact
    packedTile65536 3156744448 3156875520 14 5950 56184 32 _ _ (2187279 / 100000) (1093641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3156875520 :
    ThetaLowerSegment 3156875520 3157006592 (63136088439281 / 20000) (78923381084007 / 25000) := by
  exact
    packedTile65536 3156875520 3157006592 14 5981 56186 32 _ _ (2187283 / 100000) (1093643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157006592 :
    ThetaLowerSegment 3157006592 3157137664 (78923381084007 / 25000) (78926614442493 / 25000) := by
  exact
    packedTile65536 3157006592 3157137664 14 5913 56187 32 _ _ (273411 / 12500) (2187291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157137664 :
    ThetaLowerSegment 3157137664 3157268736 (78926614442493 / 25000) (15785978419911 / 5000) := by
  exact
    packedTile65536 3157137664 3157268736 14 5994 56188 32 _ _ (546823 / 25000) (437459 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157268736 :
    ThetaLowerSegment 3157268736 3157399808 (15785978419911 / 5000) (78933198744283 / 25000) := by
  exact
    packedTile65536 3157268736 3157399808 14 6047 56189 32 _ _ (68353 / 3125) (2187299 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157399808 :
    ThetaLowerSegment 3157399808 3157530880 (78933198744283 / 25000) (39468241761029 / 12500) := by
  exact
    packedTile65536 3157399808 3157530880 14 6007 56190 32 _ _ (21873 / 1000) (2187303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157530880 :
    ThetaLowerSegment 3157530880 3157661952 (39468241761029 / 12500) (19734938522091 / 6250) := by
  exact
    packedTile65536 3157530880 3157661952 14 5981 56191 32 _ _ (273413 / 12500) (2187307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157661952 :
    ThetaLowerSegment 3157661952 3157793024 (19734938522091 / 6250) (39471499479891 / 12500) := by
  exact
    packedTile65536 3157661952 3157793024 14 5934 56193 32 _ _ (546827 / 25000) (2187311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157793024 :
    ThetaLowerSegment 3157793024 3157924096 (39471499479891 / 12500) (39473145158757 / 12500) := by
  exact
    packedTile65536 3157793024 3157924096 14 6019 56194 32 _ _ (136707 / 6250) (437463 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3157924096 :
    ThetaLowerSegment 3157924096 3158055168 (39473145158757 / 12500) (157899118525541 / 50000) := by
  exact
    packedTile65536 3157924096 3158055168 14 5978 56195 32 _ _ (2187317 / 100000) (54683 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158055168 :
    ThetaLowerSegment 3158055168 3158186240 (157899118525541 / 50000) (39476410826021 / 12500) := by
  exact
    packedTile65536 3158055168 3158186240 14 5966 56196 32 _ _ (2187321 / 100000) (546831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158186240 :
    ThetaLowerSegment 3158186240 3158317312 (39476410826021 / 12500)
      (315824386497593 / 100000) := by
  exact
    packedTile65536 3158186240 3158317312 14 5989 56197 32 _ _ (87493 / 4000) (68354 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158317312 :
    ThetaLowerSegment 3158317312 3158448384 (315824386497593 / 100000)
      (157918778202751 / 50000) := by
  exact
    packedTile65536 3158317312 3158448384 14 6021 56198 32 _ _ (2187329 / 100000) (546833 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158448384 :
    ThetaLowerSegment 3158448384 3158579456 (157918778202751 / 50000) (63170097146173 / 20000) := by
  exact
    packedTile65536 3158448384 3158579456 14 5911 56200 32 _ _ (2187333 / 100000) (273417 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158579456 :
    ThetaLowerSegment 3158579456 3158710528 (63170097146173 / 20000) (39482950945691 / 12500) := by
  exact
    packedTile65536 3158579456 3158710528 14 5999 56201 32 _ _ (2187337 / 100000) (109367 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158710528 :
    ThetaLowerSegment 3158710528 3158841600 (39482950945691 / 12500)
      (315876733798869 / 100000) := by
  exact
    packedTile65536 3158710528 3158841600 14 6001 56202 32 _ _ (2187341 / 100000) (136709 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158841600 :
    ThetaLowerSegment 3158841600 3158972672 (315876733798869 / 100000)
      (315890072234777 / 100000) := by
  exact
    packedTile65536 3158841600 3158972672 14 6098 56203 32 _ _ (1093673 / 50000) (2187349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3158972672 :
    ThetaLowerSegment 3158972672 3159103744 (315890072234777 / 100000)
      (315903163524527 / 100000) := by
  exact
    packedTile65536 3158972672 3159103744 14 5985 56204 32 _ _ (43747 / 2000) (2187353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159103744 :
    ThetaLowerSegment 3159103744 3159234816 (315903163524527 / 100000)
      (315916132346393 / 100000) := by
  exact
    packedTile65536 3159103744 3159234816 14 5929 56205 32 _ _ (1093677 / 50000) (2187357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159234816 :
    ThetaLowerSegment 3159234816 3159365888 (315916132346393 / 100000)
      (315929249932319 / 100000) := by
  exact
    packedTile65536 3159234816 3159365888 14 5997 56207 32 _ _ (1093679 / 50000) (2187361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159365888 :
    ThetaLowerSegment 3159365888 3159496960 (315929249932319 / 100000)
      (315942317232907 / 100000) := by
  exact
    packedTile65536 3159365888 3159496960 14 5974 56208 32 _ _ (1093681 / 50000) (437473 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159496960 :
    ThetaLowerSegment 3159496960 3159628032 (315942317232907 / 100000)
      (63191056787711 / 20000) := by
  exact
    packedTile65536 3159496960 3159628032 14 5928 56209 32 _ _ (1093683 / 50000) (2187369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159628032 :
    ThetaLowerSegment 3159628032 3159759104 (63191056787711 / 20000)
      (315968368791877 / 100000) := by
  exact
    packedTile65536 3159628032 3159759104 14 5982 56210 32 _ _ (2187371 / 100000) (1093687 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159759104 :
    ThetaLowerSegment 3159759104 3159890176 (315968368791877 / 100000)
      (315981580536877 / 100000) := by
  exact
    packedTile65536 3159759104 3159890176 14 6040 56211 32 _ _ (17499 / 800) (1093689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3159890176 :
    ThetaLowerSegment 3159890176 3160021248 (315981580536877 / 100000)
      (157997303189411 / 50000) := by
  exact
    packedTile65536 3159890176 3160021248 14 5955 56212 32 _ _ (2187379 / 100000) (1093691 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160021248 :
    ThetaLowerSegment 3160021248 3160152320 (157997303189411 / 50000)
      (316007527250203 / 100000) := by
  exact
    packedTile65536 3160021248 3160152320 14 5907 56214 32 _ _ (2187383 / 100000) (1093693 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160152320 :
    ThetaLowerSegment 3160152320 3160283392 (316007527250203 / 100000)
      (316020616574011 / 100000) := by
  exact
    packedTile65536 3160152320 3160283392 14 5984 56215 32 _ _ (2187387 / 100000) (218739 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160283392 :
    ThetaLowerSegment 3160283392 3160414464 (316020616574011 / 100000)
      (158016963424123 / 50000) := by
  exact
    packedTile65536 3160283392 3160414464 14 6085 56216 32 _ _ (2187391 / 100000) (1093697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160414464 :
    ThetaLowerSegment 3160414464 3160545536 (158016963424123 / 50000)
      (158023529983913 / 50000) := by
  exact
    packedTile65536 3160414464 3160545536 14 6004 56217 32 _ _ (437479 / 20000) (1093699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160545536 :
    ThetaLowerSegment 3160545536 3160676608 (158023529983913 / 50000)
      (158030122807513 / 50000) := by
  exact
    packedTile65536 3160545536 3160676608 14 6028 56218 32 _ _ (10937 / 500) (2187403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160676608 :
    ThetaLowerSegment 3160676608 3160807680 (158030122807513 / 50000)
      (158036715643169 / 50000) := by
  exact
    packedTile65536 3160676608 3160807680 14 6028 56219 32 _ _ (546851 / 25000) (2187407 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160807680 :
    ThetaLowerSegment 3160807680 3160938752 (158036715643169 / 50000) (31608648792469 / 10000) := by
  exact
    packedTile65536 3160807680 3160938752 14 5969 56221 32 _ _ (136713 / 6250) (2187411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3160938752 :
    ThetaLowerSegment 3160938752 3161069824 (31608648792469 / 10000) (31609953583727 / 10000) := by
  exact
    packedTile65536 3160938752 3161069824 14 5965 56222 32 _ _ (546853 / 25000) (437483 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161069824 :
    ThetaLowerSegment 3161069824 3161200896 (31609953583727 / 10000) (158056359696751 / 50000) := by
  exact
    packedTile65536 3161069824 3161200896 14 6027 56223 32 _ _ (273427 / 12500) (2187419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161200896 :
    ThetaLowerSegment 3161200896 3161331968 (158056359696751 / 50000)
      (158062919769331 / 50000) := by
  exact
    packedTile65536 3161200896 3161331968 14 5998 56224 32 _ _ (109371 / 5000) (2187423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161331968 :
    ThetaLowerSegment 3161331968 3161463040 (158062919769331 / 50000)
      (158069479853907 / 50000) := by
  exact
    packedTile65536 3161331968 3161463040 14 5998 56225 32 _ _ (68357 / 3125) (2187427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161463040 :
    ThetaLowerSegment 3161463040 3161594112 (158069479853907 / 50000)
      (316152051470379 / 100000) := by
  exact
    packedTile65536 3161463040 3161594112 14 5985 56226 32 _ _ (2187429 / 100000) (273429 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161594112 :
    ThetaLowerSegment 3161594112 3161725184 (316152051470379 / 100000)
      (79041290189087 / 25000) := by
  exact
    packedTile65536 3161594112 3161725184 14 5993 56228 32 _ _ (2187433 / 100000) (546859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161725184 :
    ThetaLowerSegment 3161725184 3161856256 (79041290189087 / 25000) (39522271453953 / 12500) := by
  exact
    packedTile65536 3161725184 3161856256 14 5948 56229 32 _ _ (2187437 / 100000) (27343 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161856256 :
    ThetaLowerSegment 3161856256 3161987328 (39522271453953 / 12500)
      (316191241591599 / 100000) := by
  exact
    packedTile65536 3161856256 3161987328 14 5975 56230 32 _ _ (2187441 / 100000) (546861 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3161987328 :
    ThetaLowerSegment 3161987328 3162118400 (316191241591599 / 100000)
      (158102168912407 / 50000) := by
  exact
    packedTile65536 3161987328 3162118400 14 5987 56231 32 _ _ (437489 / 20000) (273431 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3162118400 :
    ThetaLowerSegment 3162118400 3162249472 (158102168912407 / 50000) (505947901531 / 160) := by
  exact
    packedTile65536 3162118400 3162249472 14 5989 56232 32 _ _ (2187449 / 100000) (546863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3162249472 :
    ThetaLowerSegment 3162249472 3162380544 (505947901531 / 160) (316230611298841 / 100000) := by
  exact
    packedTile65536 3162249472 3162380544 14 6022 56233 32 _ _ (2187453 / 100000) (68358 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3162380544 :
    ThetaLowerSegment 3162380544 3162511616 (316230611298841 / 100000)
      (316243569800033 / 100000) := by
  exact
    packedTile65536 3162380544 3162511616 14 5924 56235 32 _ _ (1093729 / 50000) (2187461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3162511616 :
    ThetaLowerSegment 3162511616 3162642688 (316243569800033 / 100000) (12650269182857 / 4000) := by
  exact
    packedTile65536 3162511616 3162642688 14 6016 56236 32 _ _ (1093731 / 50000) (437493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3162642688 :
    ThetaLowerSegment 3162642688 3162773760 (12650269182857 / 4000) (316269618121097 / 100000) := by
  exact
    packedTile65536 3162642688 3162773760 14 5892 56237 32 _ _ (1093733 / 50000) (2187469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3162773760 :
    ThetaLowerSegment 3162773760 3162904832 (316269618121097 / 100000)
      (316282764815797 / 100000) := by
  exact
    packedTile65536 3162773760 3162904832 14 6010 56238 32 _ _ (218747 / 10000) (2187473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3162904832 :
    ThetaLowerSegment 3162904832 3163035904 (316282764815797 / 100000)
      (316295974971283 / 100000) := by
  exact
    packedTile65536 3162904832 3163035904 14 6039 56239 32 _ _ (1093737 / 50000) (2187477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163035904 :
    ThetaLowerSegment 3163035904 3163166976 (316295974971283 / 100000)
      (316309202650749 / 100000) := by
  exact
    packedTile65536 3163035904 3163166976 14 6047 56240 32 _ _ (1093739 / 50000) (2187481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163166976 :
    ThetaLowerSegment 3163166976 3163298048 (316309202650749 / 100000)
      (316322261918289 / 100000) := by
  exact
    packedTile65536 3163166976 3163298048 14 5970 56242 32 _ _ (1093741 / 50000) (437497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163298048 :
    ThetaLowerSegment 3163298048 3163429120 (316322261918289 / 100000)
      (63267054618193 / 20000) := by
  exact
    packedTile65536 3163298048 3163429120 14 5948 56243 32 _ _ (2187487 / 100000) (218749 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163429120 :
    ThetaLowerSegment 3163429120 3163560192 (63267054618193 / 20000) (158174176049827 / 50000) := by
  exact
    packedTile65536 3163429120 3163560192 14 5979 56244 32 _ _ (2187491 / 100000) (1093747 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163560192 :
    ThetaLowerSegment 3163560192 3163691264 (158174176049827 / 50000) (19772595324659 / 6250) := by
  exact
    packedTile65536 3163560192 3163691264 14 6022 56245 32 _ _ (437499 / 20000) (1093749 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163691264 :
    ThetaLowerSegment 3163691264 3163822336 (19772595324659 / 6250) (316374613001061 / 100000) := by
  exact
    packedTile65536 3163691264 3163822336 14 5983 56246 32 _ _ (2187499 / 100000) (1093751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163822336 :
    ThetaLowerSegment 3163822336 3163953408 (316374613001061 / 100000)
      (158193902915827 / 50000) := by
  exact
    packedTile65536 3163822336 3163953408 14 6031 56247 32 _ _ (2187503 / 100000) (1093753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3163953408 :
    ThetaLowerSegment 3163953408 3164084480 (158193902915827 / 50000)
      (316400880560993 / 100000) := by
  exact
    packedTile65536 3163953408 3164084480 14 5977 56249 32 _ _ (2187507 / 100000) (218751 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3164084480 :
    ThetaLowerSegment 3164084480 3164215552 (316400880560993 / 100000)
      (158207137345423 / 50000) := by
  exact
    packedTile65536 3164084480 3164215552 14 6123 56250 32 _ _ (2187511 / 100000) (1093757 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3164215552 :
    ThetaLowerSegment 3164215552 3164346624 (158207137345423 / 50000) (31642723353563 / 10000) := by
  exact
    packedTile65536 3164215552 3164346624 14 5924 56251 32 _ _ (546879 / 25000) (2187519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3164346624 :
    ThetaLowerSegment 3164346624 3164477696 (31642723353563 / 10000) (31644043959387 / 10000) := by
  exact
    packedTile65536 3164346624 3164477696 14 6037 56252 32 _ _ (13672 / 625) (2187523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3164477696 :
    ThetaLowerSegment 3164477696 3164608768 (31644043959387 / 10000) (158226663148877 / 50000) := by
  exact
    packedTile65536 3164477696 3164608768 14 5891 56253 32 _ _ (546881 / 25000) (2187527 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3164608768 :
    ThetaLowerSegment 3164608768 3164739840 (158226663148877 / 50000) (31646640115261 / 10000) := by
  exact
    packedTile65536 3164608768 3164739840 14 5977 56254 32 _ _ (273441 / 12500) (2187531 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3164739840 :
    ThetaLowerSegment 3164739840 3164870912 (31646640115261 / 10000) (158239826610733 / 50000) := by
  exact
    packedTile65536 3164739840 3164870912 14 6058 56256 32 _ _ (546883 / 25000) (437507 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3164870912 :
    ThetaLowerSegment 3164870912 3165001984 (158239826610733 / 50000) (31649289656441 / 10000) := by
  exact
    packedTile65536 3164870912 3165001984 14 6054 56257 32 _ _ (136721 / 6250) (2187539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165001984 :
    ThetaLowerSegment 3165001984 3165133056 (31649289656441 / 10000) (6330120042331 / 2000) := by
  exact
    packedTile65536 3165001984 3165133056 14 5991 56258 32 _ _ (109377 / 5000) (2187543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165133056 :
    ThetaLowerSegment 3165133056 3165264128 (6330120042331 / 2000) (31651914488691 / 10000) := by
  exact
    packedTile65536 3165133056 3165264128 14 6008 56259 32 _ _ (437509 / 20000) (546887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165264128 :
    ThetaLowerSegment 3165264128 3165395200 (31651914488691 / 10000)
      (316532438622183 / 100000) := by
  exact
    packedTile65536 3165264128 3165395200 14 6077 56260 32 _ _ (2187549 / 100000) (68361 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165395200 :
    ThetaLowerSegment 3165395200 3165526272 (316532438622183 / 100000)
      (63309123288291 / 20000) := by
  exact
    packedTile65536 3165395200 3165526272 14 6024 56261 32 _ _ (2187553 / 100000) (546889 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165526272 :
    ThetaLowerSegment 3165526272 3165657344 (63309123288291 / 20000) (63311743981577 / 20000) := by
  exact
    packedTile65536 3165526272 3165657344 14 5990 56263 32 _ _ (2187557 / 100000) (54689 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165657344 :
    ThetaLowerSegment 3165657344 3165788416 (63311743981577 / 20000) (158285910605357 / 50000) := by
  exact
    packedTile65536 3165657344 3165788416 14 5989 56264 32 _ _ (2187561 / 100000) (546891 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165788416 :
    ThetaLowerSegment 3165788416 3165919488 (158285910605357 / 50000)
      (316585036290879 / 100000) := by
  exact
    packedTile65536 3165788416 3165919488 14 6041 56265 32 _ _ (437513 / 20000) (136723 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3165919488 :
    ThetaLowerSegment 3165919488 3166050560 (316585036290879 / 100000)
      (31659820326869 / 10000) := by
  exact
    packedTile65536 3165919488 3166050560 14 6019 56266 32 _ _ (2187569 / 100000) (546893 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166050560 :
    ThetaLowerSegment 3166050560 3166181632 (31659820326869 / 10000) (39576431675551 / 12500) := by
  exact
    packedTile65536 3166050560 3166181632 14 6057 56267 32 _ _ (1093787 / 50000) (2187577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166181632 :
    ThetaLowerSegment 3166181632 3166312704 (39576431675551 / 12500) (158312218339919 / 50000) := by
  exact
    packedTile65536 3166181632 3166312704 14 5935 56268 32 _ _ (1093789 / 50000) (2187581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166312704 :
    ThetaLowerSegment 3166312704 3166443776 (158312218339919 / 50000)
      (158318783273501 / 50000) := by
  exact
    packedTile65536 3166312704 3166443776 14 6002 56269 32 _ _ (1093791 / 50000) (437517 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166443776 :
    ThetaLowerSegment 3166443776 3166574848 (158318783273501 / 50000) (79162671375061 / 25000) := by
  exact
    packedTile65536 3166443776 3166574848 14 5997 56271 32 _ _ (1093793 / 50000) (2187589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166574848 :
    ThetaLowerSegment 3166574848 3166705920 (79162671375061 / 25000) (39582973645543 / 12500) := by
  exact
    packedTile65536 3166574848 3166705920 14 5990 56272 32 _ _ (218759 / 10000) (2187593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166705920 :
    ThetaLowerSegment 3166705920 3166836992 (39582973645543 / 12500) (39584585902321 / 12500) := by
  exact
    packedTile65536 3166705920 3166836992 14 5896 56273 32 _ _ (1093797 / 50000) (2187597 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166836992 :
    ThetaLowerSegment 3166836992 3166968064 (39584585902321 / 12500) (15834487796451 / 5000) := by
  exact
    packedTile65536 3166836992 3166968064 14 5974 56274 32 _ _ (1093799 / 50000) (2187601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3166968064 :
    ThetaLowerSegment 3166968064 3167099136 (15834487796451 / 5000) (316702813731327 / 100000) := by
  exact
    packedTile65536 3166968064 3167099136 14 5969 56275 32 _ _ (2187603 / 100000) (1093803 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167099136 :
    ThetaLowerSegment 3167099136 3167230208 (316702813731327 / 100000)
      (79178982108823 / 25000) := by
  exact
    packedTile65536 3167099136 3167230208 14 5995 56276 32 _ _ (2187607 / 100000) (218761 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167230208 :
    ThetaLowerSegment 3167230208 3167361280 (79178982108823 / 25000)
      (316729178795119 / 100000) := by
  exact
    packedTile65536 3167230208 3167361280 14 6057 56278 32 _ _ (2187611 / 100000) (1093807 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167361280 :
    ThetaLowerSegment 3167361280 3167492352 (316729178795119 / 100000)
      (39592768098653 / 12500) := by
  exact
    packedTile65536 3167361280 3167492352 14 5927 56279 32 _ _ (437523 / 20000) (1093809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167492352 :
    ThetaLowerSegment 3167492352 3167623424 (39592768098653 / 12500)
      (316755368946079 / 100000) := by
  exact
    packedTile65536 3167492352 3167623424 14 6045 56280 32 _ _ (2187619 / 100000) (1093811 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167623424 :
    ThetaLowerSegment 3167623424 3167754496 (316755368946079 / 100000)
      (79192107810753 / 25000) := by
  exact
    packedTile65536 3167623424 3167754496 14 5971 56281 32 _ _ (2187623 / 100000) (1093813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167754496 :
    ThetaLowerSegment 3167754496 3167885568 (79192107810753 / 25000) (158390780690133 / 50000) := by
  exact
    packedTile65536 3167754496 3167885568 14 6002 56282 32 _ _ (2187627 / 100000) (218763 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3167885568 :
    ThetaLowerSegment 3167885568 3168016640 (158390780690133 / 50000)
      (158397286707701 / 50000) := by
  exact
    packedTile65536 3167885568 3168016640 14 5948 56283 32 _ _ (136727 / 6250) (437527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168016640 :
    ThetaLowerSegment 3168016640 3168147712 (158397286707701 / 50000)
      (158403832114613 / 50000) := by
  exact
    packedTile65536 3168016640 3168147712 14 5984 56285 32 _ _ (546909 / 25000) (2187639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168147712 :
    ThetaLowerSegment 3168147712 3168278784 (158403832114613 / 50000)
      (158410329405413 / 50000) := by
  exact
    packedTile65536 3168147712 3168278784 14 5940 56286 32 _ _ (54691 / 2500) (2187643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168278784 :
    ThetaLowerSegment 3168278784 3168409856 (158410329405413 / 50000) (31683374310959 / 10000) := by
  exact
    packedTile65536 3168278784 3168409856 14 5981 56287 32 _ _ (546911 / 25000) (2187647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168409856 :
    ThetaLowerSegment 3168409856 3168540928 (31683374310959 / 10000) (158423438874091 / 50000) := by
  exact
    packedTile65536 3168409856 3168540928 14 6004 56288 32 _ _ (68364 / 3125) (2187651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168540928 :
    ThetaLowerSegment 3168540928 3168672000 (158423438874091 / 50000)
      (158430100274431 / 50000) := by
  exact
    packedTile65536 3168540928 3168672000 14 6090 56289 32 _ _ (546913 / 25000) (437531 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168672000 :
    ThetaLowerSegment 3168672000 3168803072 (158430100274431 / 50000)
      (158436627146107 / 50000) := by
  exact
    packedTile65536 3168672000 3168803072 14 5967 56290 32 _ _ (273457 / 12500) (2187659 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168803072 :
    ThetaLowerSegment 3168803072 3168934144 (158436627146107 / 50000)
      (158443154029717 / 50000) := by
  exact
    packedTile65536 3168803072 3168934144 14 5967 56292 32 _ _ (109383 / 5000) (2187663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3168934144 :
    ThetaLowerSegment 3168934144 3169065216 (158443154029717 / 50000)
      (158449664520757 / 50000) := by
  exact
    packedTile65536 3168934144 3169065216 14 5952 56293 32 _ _ (437533 / 20000) (546917 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169065216 :
    ThetaLowerSegment 3169065216 3169196288 (158449664520757 / 50000) (1980703035518 / 625) := by
  exact
    packedTile65536 3169065216 3169196288 14 6014 56294 32 _ _ (2187669 / 100000) (273459 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169196288 :
    ThetaLowerSegment 3169196288 3169327360 (1980703035518 / 625) (79231365739779 / 25000) := by
  exact
    packedTile65536 3169196288 3169327360 14 5932 56295 32 _ _ (2187673 / 100000) (546919 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169327360 :
    ThetaLowerSegment 3169327360 3169458432 (79231365739779 / 25000)
      (316938744346183 / 100000) := by
  exact
    packedTile65536 3169327360 3169458432 14 6071 56296 32 _ _ (2187677 / 100000) (13673 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169458432 :
    ThetaLowerSegment 3169458432 3169589504 (316938744346183 / 100000)
      (158476004128043 / 50000) := by
  exact
    packedTile65536 3169458432 3169589504 14 6063 56297 32 _ _ (2187681 / 100000) (546921 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169589504 :
    ThetaLowerSegment 3169589504 3169720576 (158476004128043 / 50000)
      (158482501552493 / 50000) := by
  exact
    packedTile65536 3169589504 3169720576 14 5940 56299 32 _ _ (437537 / 20000) (273461 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169720576 :
    ThetaLowerSegment 3169720576 3169851648 (158482501552493 / 50000)
      (316978227684991 / 100000) := by
  exact
    packedTile65536 3169720576 3169851648 14 6045 56300 32 _ _ (2187689 / 100000) (546923 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169851648 :
    ThetaLowerSegment 3169851648 3169982720 (316978227684991 / 100000)
      (316991264153537 / 100000) := by
  exact
    packedTile65536 3169851648 3169982720 14 5959 56301 32 _ _ (1093847 / 50000) (2187697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3169982720 :
    ThetaLowerSegment 3169982720 3170113792 (316991264153537 / 100000)
      (317004265642751 / 100000) := by
  exact
    packedTile65536 3169982720 3170113792 14 5943 56302 32 _ _ (1093849 / 50000) (2187701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3170113792 :
    ThetaLowerSegment 3170113792 3170244864 (317004265642751 / 100000) (2536138907317 / 800) := by
  exact
    packedTile65536 3170113792 3170244864 14 5987 56303 32 _ _ (1093851 / 50000) (437541 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3170244864 :
    ThetaLowerSegment 3170244864 3170375936 (2536138907317 / 800) (317030417456327 / 100000) := by
  exact
    packedTile65536 3170244864 3170375936 14 5967 56304 32 _ _ (1093853 / 50000) (2187709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3170375936 :
    ThetaLowerSegment 3170375936 3170507008 (317030417456327 / 100000)
      (317043486835867 / 100000) := by
  exact
    packedTile65536 3170375936 3170507008 14 5974 56306 32 _ _ (218771 / 10000) (2187713 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3170507008 :
    ThetaLowerSegment 3170507008 3170638080 (317043486835867 / 100000)
      (317056700628427 / 100000) := by
  exact
    packedTile65536 3170507008 3170638080 14 6040 56307 32 _ _ (1093857 / 50000) (2187717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3170638080 :
    ThetaLowerSegment 3170638080 3170769152 (317056700628427 / 100000)
      (317069798496093 / 100000) := by
  exact
    packedTile65536 3170638080 3170769152 14 5987 56308 32 _ _ (1093859 / 50000) (2187721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3170769152 :
    ThetaLowerSegment 3170769152 3170900224 (317069798496093 / 100000)
      (158541474449523 / 50000) := by
  exact
    packedTile65536 3170769152 3170900224 14 6011 56309 32 _ _ (2187723 / 100000) (1093863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3170900224 :
    ThetaLowerSegment 3170900224 3171031296 (158541474449523 / 50000) (12683845373187 / 4000) := by
  exact
    packedTile65536 3170900224 3171031296 14 6027 56310 32 _ _ (2187727 / 100000) (218773 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171031296 :
    ThetaLowerSegment 3171031296 3171162368 (12683845373187 / 4000) (158554557068849 / 50000) := by
  exact
    packedTile65536 3171031296 3171162368 14 5933 56311 32 _ _ (2187731 / 100000) (1093867 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171162368 :
    ThetaLowerSegment 3171162368 3171293440 (158554557068849 / 50000) (79280589671347 / 25000) := by
  exact
    packedTile65536 3171162368 3171293440 14 6054 56313 32 _ _ (437547 / 20000) (1093869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171293440 :
    ThetaLowerSegment 3171293440 3171424512 (79280589671347 / 25000) (39641949860227 / 12500) := by
  exact
    packedTile65536 3171293440 3171424512 14 6052 56314 32 _ _ (2187739 / 100000) (1093871 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171424512 :
    ThetaLowerSegment 3171424512 3171555584 (39641949860227 / 12500)
      (317148570010063 / 100000) := by
  exact
    packedTile65536 3171424512 3171555584 14 5929 56315 32 _ _ (2187743 / 100000) (1093873 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171555584 :
    ThetaLowerSegment 3171555584 3171686656 (317148570010063 / 100000) (2537291751731 / 800) := by
  exact
    packedTile65536 3171555584 3171686656 14 5896 56316 32 _ _ (2187747 / 100000) (8751 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171686656 :
    ThetaLowerSegment 3171686656 3171817728 (2537291751731 / 800) (317174634851893 / 100000) := by
  exact
    packedTile65536 3171686656 3171817728 14 6018 56317 32 _ _ (2187751 / 100000) (1093877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171817728 :
    ThetaLowerSegment 3171817728 3171948800 (317174634851893 / 100000)
      (317187816081793 / 100000) := by
  exact
    packedTile65536 3171817728 3171948800 14 6025 56318 32 _ _ (546939 / 25000) (2187759 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3171948800 :
    ThetaLowerSegment 3171948800 3172079872 (317187816081793 / 100000)
      (317200811376193 / 100000) := by
  exact
    packedTile65536 3171948800 3172079872 14 5940 56320 32 _ _ (27347 / 1250) (2187763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172079872 :
    ThetaLowerSegment 3172079872 3172210944 (317200811376193 / 100000)
      (317213972964417 / 100000) := by
  exact
    packedTile65536 3172079872 3172210944 14 6016 56321 32 _ _ (546941 / 25000) (2187767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172210944 :
    ThetaLowerSegment 3172210944 3172342016 (317213972964417 / 100000)
      (317227060192593 / 100000) := by
  exact
    packedTile65536 3172210944 3172342016 14 5982 56322 32 _ _ (273471 / 12500) (2187771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172342016 :
    ThetaLowerSegment 3172342016 3172473088 (317227060192593 / 100000)
      (317240114628117 / 100000) := by
  exact
    packedTile65536 3172342016 3172473088 14 5967 56323 32 _ _ (546943 / 25000) (87511 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172473088 :
    ThetaLowerSegment 3172473088 3172604160 (317240114628117 / 100000)
      (317253252222997 / 100000) := by
  exact
    packedTile65536 3172473088 3172604160 14 6005 56324 32 _ _ (68368 / 3125) (2187779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172604160 :
    ThetaLowerSegment 3172604160 3172735232 (317253252222997 / 100000)
      (317266396405237 / 100000) := by
  exact
    packedTile65536 3172604160 3172735232 14 6008 56325 32 _ _ (109389 / 5000) (2187783 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172735232 :
    ThetaLowerSegment 3172735232 3172866304 (317266396405237 / 100000)
      (317279726573149 / 100000) := by
  exact
    packedTile65536 3172735232 3172866304 14 6093 56327 32 _ _ (273473 / 12500) (2187787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172866304 :
    ThetaLowerSegment 3172866304 3172997376 (317279726573149 / 100000)
      (317292656406139 / 100000) := by
  exact
    packedTile65536 3172866304 3172997376 14 5910 56328 32 _ _ (2187789 / 100000) (136737 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3172997376 :
    ThetaLowerSegment 3172997376 3173128448 (317292656406139 / 100000)
      (63461148756773 / 20000) := by
  exact
    packedTile65536 3172997376 3173128448 14 5982 56329 32 _ _ (2187793 / 100000) (546949 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3173128448 :
    ThetaLowerSegment 3173128448 3173259520 (63461148756773 / 20000)
      (317318879317053 / 100000) := by
  exact
    packedTile65536 3173128448 3173259520 14 6004 56330 32 _ _ (2187797 / 100000) (10939 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3173259520 :
    ThetaLowerSegment 3173259520 3173390592 (317318879317053 / 100000)
      (158665951648203 / 50000) := by
  exact
    packedTile65536 3173259520 3173390592 14 5953 56331 32 _ _ (2187801 / 100000) (546951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3173390592 :
    ThetaLowerSegment 3173390592 3173521664 (158665951648203 / 50000) (79336265188919 / 25000) := by
  exact
    packedTile65536 3173390592 3173521664 14 6014 56332 32 _ _ (437561 / 20000) (68369 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3173521664 :
    ThetaLowerSegment 3173521664 3173652736 (79336265188919 / 25000) (158678934094781 / 50000) := by
  exact
    packedTile65536 3173521664 3173652736 14 5854 56334 32 _ _ (2187809 / 100000) (546953 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3173652736 :
    ThetaLowerSegment 3173652736 3173783808 (158678934094781 / 50000)
      (317371102270399 / 100000) := by
  exact
    packedTile65536 3173652736 3173783808 14 6049 56335 32 _ _ (2187813 / 100000) (273477 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3173783808 :
    ThetaLowerSegment 3173783808 3173914880 (317371102270399 / 100000)
      (317384275122577 / 100000) := by
  exact
    packedTile65536 3173783808 3173914880 14 6021 56336 32 _ _ (1093909 / 50000) (2187821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3173914880 :
    ThetaLowerSegment 3173914880 3174045952 (317384275122577 / 100000)
      (63479471222063 / 20000) := by
  exact
    packedTile65536 3173914880 3174045952 14 5979 56337 32 _ _ (1093911 / 50000) (87513 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174045952 :
    ThetaLowerSegment 3174045952 3174177024 (63479471222063 / 20000)
      (317410491817619 / 100000) := by
  exact
    packedTile65536 3174045952 3174177024 14 6004 56338 32 _ _ (1093913 / 50000) (2187829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174177024 :
    ThetaLowerSegment 3174177024 3174308096 (317410491817619 / 100000)
      (317423535660079 / 100000) := by
  exact
    packedTile65536 3174177024 3174308096 14 5962 56339 32 _ _ (218783 / 10000) (2187833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174308096 :
    ThetaLowerSegment 3174308096 3174439168 (317423535660079 / 100000)
      (63487303653407 / 20000) := by
  exact
    packedTile65536 3174308096 3174439168 14 5934 56340 32 _ _ (1093917 / 50000) (2187837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174439168 :
    ThetaLowerSegment 3174439168 3174570240 (63487303653407 / 20000)
      (317449498709889 / 100000) := by
  exact
    packedTile65536 3174439168 3174570240 14 5933 56342 32 _ _ (1093919 / 50000) (2187841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174570240 :
    ThetaLowerSegment 3174570240 3174701312 (317449498709889 / 100000)
      (63492565846239 / 20000) := by
  exact
    packedTile65536 3174570240 3174701312 14 6093 56343 32 _ _ (1093921 / 50000) (437569 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174701312 :
    ThetaLowerSegment 3174701312 3174832384 (63492565846239 / 20000)
      (317475899423199 / 100000) := by
  exact
    packedTile65536 3174701312 3174832384 14 5974 56344 32 _ _ (1093923 / 50000) (2187849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174832384 :
    ThetaLowerSegment 3174832384 3174963456 (317475899423199 / 100000)
      (317488890882437 / 100000) := by
  exact
    packedTile65536 3174832384 3174963456 14 5938 56345 32 _ _ (2187851 / 100000) (1093927 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3174963456 :
    ThetaLowerSegment 3174963456 3175094528 (317488890882437 / 100000)
      (317502109902347 / 100000) := by
  exact
    packedTile65536 3174963456 3175094528 14 6042 56346 32 _ _ (437571 / 20000) (1093929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175094528 :
    ThetaLowerSegment 3175094528 3175225600 (317502109902347 / 100000)
      (317515136414833 / 100000) := by
  exact
    packedTile65536 3175094528 3175225600 14 5954 56347 32 _ _ (2187859 / 100000) (1093931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175225600 :
    ThetaLowerSegment 3175225600 3175356672 (317515136414833 / 100000)
      (317528394864613 / 100000) := by
  exact
    packedTile65536 3175225600 3175356672 14 6060 56349 32 _ _ (2187863 / 100000) (1093933 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175356672 :
    ThetaLowerSegment 3175356672 3175487744 (317528394864613 / 100000)
      (317541312031381 / 100000) := by
  exact
    packedTile65536 3175356672 3175487744 14 5904 56350 32 _ _ (2187867 / 100000) (218787 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175487744 :
    ThetaLowerSegment 3175487744 3175618816 (317541312031381 / 100000)
      (63510854595837 / 20000) := by
  exact
    packedTile65536 3175487744 3175618816 14 5924 56351 32 _ _ (2187871 / 100000) (1093937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175618816 :
    ThetaLowerSegment 3175618816 3175749888 (63510854595837 / 20000) (63513469544037 / 20000) := by
  exact
    packedTile65536 3175618816 3175749888 14 5976 56352 32 _ _ (17503 / 800) (1093939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175749888 :
    ThetaLowerSegment 3175749888 3175880960 (63513469544037 / 20000) (158790162015267 / 50000) := by
  exact
    packedTile65536 3175749888 3175880960 14 5931 56353 32 _ _ (2187879 / 100000) (1093941 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3175880960 :
    ThetaLowerSegment 3175880960 3176012032 (158790162015267 / 50000)
      (158796674251993 / 50000) := by
  exact
    packedTile65536 3175880960 3176012032 14 5953 56354 32 _ _ (546971 / 25000) (2187887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176012032 :
    ThetaLowerSegment 3176012032 3176143104 (158796674251993 / 50000)
      (158803278391921 / 50000) := by
  exact
    packedTile65536 3176012032 3176143104 14 6037 56356 32 _ _ (136743 / 6250) (2187891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176143104 :
    ThetaLowerSegment 3176143104 3176274176 (158803278391921 / 50000)
      (158809869416571 / 50000) := by
  exact
    packedTile65536 3176143104 3176274176 14 6025 56357 32 _ _ (546973 / 25000) (437579 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176274176 :
    ThetaLowerSegment 3176274176 3176405248 (158809869416571 / 50000) (31763298216763 / 10000) := by
  exact
    packedTile65536 3176274176 3176405248 14 6053 56358 32 _ _ (273487 / 12500) (2187899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176405248 :
    ThetaLowerSegment 3176405248 3176536320 (31763298216763 / 10000) (31764606580963 / 10000) := by
  exact
    packedTile65536 3176405248 3176536320 14 5980 56359 32 _ _ (21879 / 1000) (2187903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176536320 :
    ThetaLowerSegment 3176536320 3176667392 (31764606580963 / 10000) (158829529885743 / 50000) := by
  exact
    packedTile65536 3176536320 3176667392 14 5939 56360 32 _ _ (68372 / 3125) (2187907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176667392 :
    ThetaLowerSegment 3176667392 3176798464 (158829529885743 / 50000)
      (158836122052547 / 50000) := by
  exact
    packedTile65536 3176667392 3176798464 14 6026 56361 32 _ _ (546977 / 25000) (2187911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176798464 :
    ThetaLowerSegment 3176798464 3176929536 (158836122052547 / 50000)
      (158842635466571 / 50000) := by
  exact
    packedTile65536 3176798464 3176929536 14 5954 56363 32 _ _ (273489 / 12500) (437583 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3176929536 :
    ThetaLowerSegment 3176929536 3177060608 (158842635466571 / 50000) (79424594138993 / 25000) := by
  exact
    packedTile65536 3176929536 3177060608 14 5990 56364 32 _ _ (2187917 / 100000) (27349 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177060608 :
    ThetaLowerSegment 3177060608 3177191680 (79424594138993 / 25000)
      (317711589410891 / 100000) := by
  exact
    packedTile65536 3177060608 3177191680 14 6039 56365 32 _ _ (2187921 / 100000) (546981 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177191680 :
    ThetaLowerSegment 3177191680 3177322752 (317711589410891 / 100000)
      (79431199478529 / 25000) := by
  exact
    packedTile65536 3177191680 3177322752 14 6037 56366 32 _ _ (87517 / 4000) (273491 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177322752 :
    ThetaLowerSegment 3177322752 3177339136 (79431199478529 / 25000) (158863197551143 / 50000) := by
  exact
    packedTile65536 3177322752 3177339136 11 730 56367 32 _ _ (2187929 / 100000) (546983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell3177339136 :
    ThetaLowerSegment 3177339136 3177341184 (158863197551143 / 50000) (31772660514347 / 10000) := by
  exact
    packedTile65536 3177339136 3177341184 8 96 56367 32 _ _ (2187929 / 100000) (546983 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_3145341184_3177341184 :
    ThetaLowerSegment 3145341184 3177341184 (314525997612409 / 100000)
      (31772660514347 / 10000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3145341184 cell3145472256)
                  (ThetaLowerSegment.join cell3145603328 cell3145734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3145865472 cell3145996544)
                  (ThetaLowerSegment.join cell3146127616 cell3146258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3146389760 cell3146520832)
                  (ThetaLowerSegment.join cell3146651904 cell3146782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3146914048 cell3147045120)
                  (ThetaLowerSegment.join cell3147176192 cell3147307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3147438336 cell3147569408)
                  (ThetaLowerSegment.join cell3147700480 cell3147831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3147962624 cell3148093696)
                  (ThetaLowerSegment.join cell3148224768 cell3148355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3148486912 cell3148617984)
                  (ThetaLowerSegment.join cell3148749056 cell3148880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3149011200 cell3149142272)
                  (ThetaLowerSegment.join cell3149273344 cell3149404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3149535488 cell3149666560)
                  (ThetaLowerSegment.join cell3149797632 cell3149928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3150059776 cell3150190848)
                  (ThetaLowerSegment.join cell3150321920 cell3150452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3150584064 cell3150715136)
                  (ThetaLowerSegment.join cell3150846208 cell3150977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3151108352 cell3151239424)
                  (ThetaLowerSegment.join cell3151370496 cell3151501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3151632640 cell3151763712)
                  (ThetaLowerSegment.join cell3151894784 cell3152025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3152156928 cell3152288000)
                  (ThetaLowerSegment.join cell3152419072 cell3152550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3152681216 cell3152812288)
                  (ThetaLowerSegment.join cell3152943360 cell3153074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3153205504 cell3153336576)
                  (ThetaLowerSegment.join cell3153467648 cell3153598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3153729792 cell3153860864)
                  (ThetaLowerSegment.join cell3153991936 cell3154123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3154254080 cell3154385152)
                  (ThetaLowerSegment.join cell3154516224 cell3154647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3154778368 cell3154909440)
                  (ThetaLowerSegment.join cell3155040512 cell3155171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3155302656 cell3155433728)
                  (ThetaLowerSegment.join cell3155564800 cell3155695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3155826944 cell3155958016)
                  (ThetaLowerSegment.join cell3156089088 cell3156220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3156351232 cell3156482304)
                  (ThetaLowerSegment.join cell3156613376 cell3156744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3156875520 cell3157006592)
                  (ThetaLowerSegment.join cell3157137664 cell3157268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3157399808 cell3157530880)
                  (ThetaLowerSegment.join cell3157661952 cell3157793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3157924096 cell3158055168)
                  (ThetaLowerSegment.join cell3158186240 cell3158317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3158448384 cell3158579456)
                  (ThetaLowerSegment.join cell3158710528 cell3158841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3158972672 cell3159103744)
                  (ThetaLowerSegment.join cell3159234816 cell3159365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3159496960 cell3159628032)
                  (ThetaLowerSegment.join cell3159759104 cell3159890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3160021248 cell3160152320)
                  (ThetaLowerSegment.join cell3160283392 cell3160414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3160545536 cell3160676608)
                  (ThetaLowerSegment.join cell3160807680 cell3160938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3161069824 cell3161200896)
                  (ThetaLowerSegment.join cell3161331968 cell3161463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3161594112 cell3161725184)
                  (ThetaLowerSegment.join cell3161856256 cell3161987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3162118400 cell3162249472)
                  (ThetaLowerSegment.join cell3162380544 cell3162511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3162642688 cell3162773760)
                  (ThetaLowerSegment.join cell3162904832 cell3163035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3163166976 cell3163298048)
                  (ThetaLowerSegment.join cell3163429120 cell3163560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3163691264 cell3163822336)
                  (ThetaLowerSegment.join cell3163953408 cell3164084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3164215552 cell3164346624)
                  (ThetaLowerSegment.join cell3164477696 cell3164608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3164739840 cell3164870912)
                  (ThetaLowerSegment.join cell3165001984 cell3165133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3165264128 cell3165395200)
                  (ThetaLowerSegment.join cell3165526272 cell3165657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3165788416 cell3165919488)
                  (ThetaLowerSegment.join cell3166050560 cell3166181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3166312704 cell3166443776)
                  (ThetaLowerSegment.join cell3166574848 cell3166705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3166836992 cell3166968064)
                  (ThetaLowerSegment.join cell3167099136 cell3167230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3167361280 cell3167492352)
                  (ThetaLowerSegment.join cell3167623424 cell3167754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3167885568 cell3168016640)
                  (ThetaLowerSegment.join cell3168147712 cell3168278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3168409856 cell3168540928)
                  (ThetaLowerSegment.join cell3168672000 cell3168803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3168934144 cell3169065216)
                  (ThetaLowerSegment.join cell3169196288 cell3169327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3169458432 cell3169589504)
                  (ThetaLowerSegment.join cell3169720576 cell3169851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3169982720 cell3170113792)
                  (ThetaLowerSegment.join cell3170244864 cell3170375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3170507008 cell3170638080)
                  (ThetaLowerSegment.join cell3170769152 cell3170900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3171031296 cell3171162368)
                  (ThetaLowerSegment.join cell3171293440 cell3171424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3171555584 cell3171686656)
                  (ThetaLowerSegment.join cell3171817728 cell3171948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3172079872 cell3172210944)
                  (ThetaLowerSegment.join cell3172342016 cell3172473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3172604160 cell3172735232)
                  (ThetaLowerSegment.join cell3172866304 cell3172997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3173128448 cell3173259520)
                  (ThetaLowerSegment.join cell3173390592 cell3173521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3173652736 cell3173783808)
                  (ThetaLowerSegment.join cell3173914880 cell3174045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3174177024 cell3174308096)
                  (ThetaLowerSegment.join cell3174439168 cell3174570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3174701312 cell3174832384)
                  (ThetaLowerSegment.join cell3174963456 cell3175094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3175225600 cell3175356672)
                  (ThetaLowerSegment.join cell3175487744 cell3175618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3175749888 cell3175880960)
                  (ThetaLowerSegment.join cell3176012032 cell3176143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell3176274176 cell3176405248)
                  (ThetaLowerSegment.join cell3176536320 cell3176667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell3176798464 cell3176929536)
                (ThetaLowerSegment.join cell3177060608 cell3177191680))
              (ThetaLowerSegment.join cell3177322752 cell3177339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
