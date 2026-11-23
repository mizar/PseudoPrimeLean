/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2825341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2793341184 :
    ThetaLowerSegment 2793341184 2793472256 (55865469650827 / 20000) (8729395135271 / 3125) := by
  exact
    packedTile65536 2793341184 2793472256 14 6113 52852 31 _ _ (2175049 / 100000) (543763 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793472256 :
    ThetaLowerSegment 2793472256 2793603328 (8729395135271 / 3125) (69838418225533 / 25000) := by
  exact
    packedTile65536 2793472256 2793603328 14 5990 52853 31 _ _ (1087527 / 50000) (2175057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793603328 :
    ThetaLowerSegment 2793603328 2793734400 (69838418225533 / 25000) (17460419931251 / 6250) := by
  exact
    packedTile65536 2793603328 2793734400 14 5998 52854 31 _ _ (1087529 / 50000) (2175061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793734400 :
    ThetaLowerSegment 2793734400 2793865472 (17460419931251 / 6250) (11175194512229 / 4000) := by
  exact
    packedTile65536 2793734400 2793865472 14 6043 52855 31 _ _ (2175063 / 100000) (1087533 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793865472 :
    ThetaLowerSegment 2793865472 2793996544 (11175194512229 / 4000) (279392963240289 / 100000) := by
  exact
    packedTile65536 2793865472 2793996544 14 6023 52857 31 _ _ (543767 / 25000) (2175071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2793996544 :
    ThetaLowerSegment 2793996544 2794127616 (279392963240289 / 100000)
      (279406094149953 / 100000) := by
  exact
    packedTile65536 2793996544 2794127616 14 6037 52858 31 _ _ (67971 / 3125) (87003 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794127616 :
    ThetaLowerSegment 2794127616 2794258688 (279406094149953 / 100000)
      (55883818482021 / 20000) := by
  exact
    packedTile65536 2794127616 2794258688 14 5976 52859 31 _ _ (2175077 / 100000) (54377 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794258688 :
    ThetaLowerSegment 2794258688 2794389760 (55883818482021 / 20000)
      (279432081999809 / 100000) := by
  exact
    packedTile65536 2794258688 2794389760 14 5972 52860 31 _ _ (1087541 / 50000) (435017 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794389760 :
    ThetaLowerSegment 2794389760 2794520832 (279432081999809 / 100000)
      (55889033463437 / 20000) := by
  exact
    packedTile65536 2794389760 2794520832 14 6016 52861 31 _ _ (1087543 / 50000) (2175089 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794520832 :
    ThetaLowerSegment 2794520832 2794651904 (55889033463437 / 20000) (139729151345867 / 50000) := by
  exact
    packedTile65536 2794520832 2794651904 14 6039 52863 31 _ _ (2175091 / 100000) (1087547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794651904 :
    ThetaLowerSegment 2794651904 2794782976 (139729151345867 / 50000) (27947140982023 / 10000) := by
  exact
    packedTile65536 2794651904 2794782976 14 6026 52864 31 _ _ (271887 / 12500) (2175099 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794782976 :
    ThetaLowerSegment 2794782976 2794914048 (27947140982023 / 10000)
      (279484423449513 / 100000) := by
  exact
    packedTile65536 2794782976 2794914048 14 5983 52865 31 _ _ (2175101 / 100000) (67972 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2794914048 :
    ThetaLowerSegment 2794914048 2795045120 (279484423449513 / 100000)
      (279497526282033 / 100000) := by
  exact
    packedTile65536 2794914048 2795045120 14 6024 52866 31 _ _ (435021 / 20000) (543777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795045120 :
    ThetaLowerSegment 2795045120 2795176192 (279497526282033 / 100000)
      (279510709623743 / 100000) := by
  exact
    packedTile65536 2795045120 2795176192 14 6061 52868 31 _ _ (217511 / 10000) (2175113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795176192 :
    ThetaLowerSegment 2795176192 2795307264 (279510709623743 / 100000)
      (69880969986267 / 25000) := by
  exact
    packedTile65536 2795176192 2795307264 14 6055 52869 31 _ _ (435023 / 20000) (1087559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795307264 :
    ThetaLowerSegment 2795307264 2795438336 (69880969986267 / 25000) (139768558859651 / 50000) := by
  exact
    packedTile65536 2795307264 2795438336 14 6086 52870 31 _ _ (2175119 / 100000) (1087561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795438336 :
    ThetaLowerSegment 2795438336 2795569408 (139768558859651 / 50000)
      (139775098369957 / 50000) := by
  exact
    packedTile65536 2795438336 2795569408 14 6013 52871 31 _ _ (543781 / 25000) (2175127 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795569408 :
    ThetaLowerSegment 2795569408 2795700480 (139775098369957 / 50000)
      (279563301892139 / 100000) := by
  exact
    packedTile65536 2795569408 2795700480 14 6025 52873 31 _ _ (2175129 / 100000) (543783 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795700480 :
    ThetaLowerSegment 2795700480 2795831552 (279563301892139 / 100000)
      (279576439695459 / 100000) := by
  exact
    packedTile65536 2795700480 2795831552 14 6040 52874 31 _ _ (2175133 / 100000) (67973 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795831552 :
    ThetaLowerSegment 2795831552 2795962624 (279576439695459 / 100000)
      (279589333913523 / 100000) := by
  exact
    packedTile65536 2795831552 2795962624 14 5928 52875 31 _ _ (1087569 / 50000) (2175141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2795962624 :
    ThetaLowerSegment 2795962624 2796093696 (279589333913523 / 100000)
      (279602506579531 / 100000) := by
  exact
    packedTile65536 2795962624 2796093696 14 6056 52876 31 _ _ (2175143 / 100000) (1087573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2796093696 :
    ThetaLowerSegment 2796093696 2796224768 (279602506579531 / 100000)
      (279615705371527 / 100000) := by
  exact
    packedTile65536 2796093696 2796224768 14 6068 52878 31 _ _ (2175147 / 100000) (43503 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2796224768 :
    ThetaLowerSegment 2796224768 2796355840 (279615705371527 / 100000)
      (279628817187783 / 100000) := by
  exact
    packedTile65536 2796224768 2796355840 14 6028 52879 31 _ _ (135947 / 6250) (435031 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2796355840 :
    ThetaLowerSegment 2796355840 2796486912 (279628817187783 / 100000)
      (279641898581981 / 100000) := by
  exact
    packedTile65536 2796355840 2796486912 14 6014 52880 31 _ _ (2175157 / 100000) (54379 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2796486912 :
    ThetaLowerSegment 2796486912 2796617984 (279641898581981 / 100000)
      (69913762945137 / 25000) := by
  exact
    packedTile65536 2796486912 2796617984 14 6047 52881 31 _ _ (2175161 / 100000) (543791 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2796617984 :
    ThetaLowerSegment 2796617984 2796749056 (69913762945137 / 25000) (27966807449939 / 10000) := by
  exact
    packedTile65536 2796617984 2796749056 14 5987 52883 31 _ _ (1087583 / 50000) (2175169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2796749056 :
    ThetaLowerSegment 2796749056 2796880128 (27966807449939 / 10000) (69920299870301 / 25000) := by
  exact
    packedTile65536 2796749056 2796880128 14 6034 52884 31 _ _ (2175171 / 100000) (1087587 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2796880128 :
    ThetaLowerSegment 2796880128 2797011200 (69920299870301 / 25000) (69923543057717 / 25000) := by
  exact
    packedTile65536 2796880128 2797011200 14 5964 52885 31 _ _ (271897 / 12500) (2175179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797011200 :
    ThetaLowerSegment 2797011200 2797142272 (69923543057717 / 25000) (8740855690594 / 3125) := by
  exact
    packedTile65536 2797011200 2797142272 14 6073 52886 31 _ _ (108759 / 5000) (2175183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797142272 :
    ThetaLowerSegment 2797142272 2797273344 (8740855690594 / 3125) (279720474537523 / 100000) := by
  exact
    packedTile65536 2797142272 2797273344 14 6019 52888 31 _ _ (435037 / 20000) (543797 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797273344 :
    ThetaLowerSegment 2797273344 2797404416 (279720474537523 / 100000)
      (279733617035503 / 100000) := by
  exact
    packedTile65536 2797273344 2797404416 14 6042 52889 31 _ _ (217519 / 10000) (2175193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797404416 :
    ThetaLowerSegment 2797404416 2797535488 (279733617035503 / 100000)
      (279746863966963 / 100000) := by
  exact
    packedTile65536 2797404416 2797535488 14 6090 52890 31 _ _ (1087597 / 50000) (2175197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797535488 :
    ThetaLowerSegment 2797535488 2797666560 (279746863966963 / 100000)
      (55951995213307 / 20000) := by
  exact
    packedTile65536 2797535488 2797666560 14 6028 52891 31 _ _ (2175199 / 100000) (1087601 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797666560 :
    ThetaLowerSegment 2797666560 2797797632 (55951995213307 / 20000)
      (279773138225939 / 100000) := by
  exact
    packedTile65536 2797666560 2797797632 14 6051 52892 31 _ _ (543801 / 25000) (2175207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797797632 :
    ThetaLowerSegment 2797797632 2797928704 (279773138225939 / 100000)
      (55957253991327 / 20000) := by
  exact
    packedTile65536 2797797632 2797928704 14 6037 52894 31 _ _ (271901 / 12500) (2175211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2797928704 :
    ThetaLowerSegment 2797928704 2798059776 (55957253991327 / 20000) (55959912101613 / 20000) := by
  exact
    packedTile65536 2797928704 2798059776 14 6110 52895 31 _ _ (2175213 / 100000) (135951 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798059776 :
    ThetaLowerSegment 2798059776 2798190848 (55959912101613 / 20000) (55962511487123 / 20000) := by
  exact
    packedTile65536 2798059776 2798190848 14 5975 52896 31 _ _ (1087609 / 50000) (2175221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798190848 :
    ThetaLowerSegment 2798190848 2798321920 (55962511487123 / 20000)
      (279825621818947 / 100000) := by
  exact
    packedTile65536 2798190848 2798321920 14 6006 52897 31 _ _ (1087611 / 50000) (87009 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798321920 :
    ThetaLowerSegment 2798321920 2798452992 (279825621818947 / 100000)
      (279838712335033 / 100000) := by
  exact
    packedTile65536 2798321920 2798452992 14 6018 52899 31 _ _ (2175227 / 100000) (217523 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798452992 :
    ThetaLowerSegment 2798452992 2798584064 (279838712335033 / 100000)
      (279851818107833 / 100000) := by
  exact
    packedTile65536 2798452992 2798584064 14 6025 52900 31 _ _ (67976 / 3125) (435047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798584064 :
    ThetaLowerSegment 2798584064 2798715136 (279851818107833 / 100000) (11194603220869 / 4000) := by
  exact
    packedTile65536 2798584064 2798715136 14 6097 52901 31 _ _ (543809 / 25000) (2175239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798715136 :
    ThetaLowerSegment 2798715136 2798846208 (11194603220869 / 4000) (27987805583429 / 10000) := by
  exact
    packedTile65536 2798715136 2798846208 14 5965 52902 31 _ _ (2175241 / 100000) (543811 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798846208 :
    ThetaLowerSegment 2798846208 2798977280 (27987805583429 / 10000) (139945527552193 / 50000) := by
  exact
    packedTile65536 2798846208 2798977280 14 5976 52904 31 _ _ (1087623 / 50000) (2175249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2798977280 :
    ThetaLowerSegment 2798977280 2799108352 (139945527552193 / 50000) (8747000544348 / 3125) := by
  exact
    packedTile65536 2798977280 2799108352 14 5959 52905 31 _ _ (8701 / 400) (2175253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2799108352 :
    ThetaLowerSegment 2799108352 2799239424 (8747000544348 / 3125) (279917223392241 / 100000) := by
  exact
    packedTile65536 2799108352 2799239424 14 6071 52906 31 _ _ (435051 / 20000) (1087629 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2799239424 :
    ThetaLowerSegment 2799239424 2799370496 (279917223392241 / 100000)
      (279930268426461 / 100000) := by
  exact
    packedTile65536 2799239424 2799370496 14 5997 52907 31 _ _ (108763 / 5000) (2175263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2799370496 :
    ThetaLowerSegment 2799370496 2799501568 (279930268426461 / 100000)
      (139971617590563 / 50000) := by
  exact
    packedTile65536 2799370496 2799501568 14 5961 52909 31 _ _ (435053 / 20000) (543817 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2799501568 :
    ThetaLowerSegment 2799501568 2799632640 (139971617590563 / 50000)
      (279956545652137 / 100000) := by
  exact
    packedTile65536 2799501568 2799632640 14 6119 52910 31 _ _ (2175269 / 100000) (271909 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2799632640 :
    ThetaLowerSegment 2799632640 2799763712 (279956545652137 / 100000)
      (279969586419767 / 100000) := by
  exact
    packedTile65536 2799632640 2799763712 14 5995 52911 31 _ _ (1087637 / 50000) (2175277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2799763712 :
    ThetaLowerSegment 2799763712 2799894784 (279969586419767 / 100000) (2799826968263 / 1000) := by
  exact
    packedTile65536 2799763712 2799894784 14 6027 52912 31 _ _ (2175279 / 100000) (1087641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2799894784 :
    ThetaLowerSegment 2799894784 2800025856 (2799826968263 / 1000) (11199827765689 / 4000) := by
  exact
    packedTile65536 2799894784 2800025856 14 5975 52914 31 _ _ (2175283 / 100000) (1087643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800025856 :
    ThetaLowerSegment 2800025856 2800156928 (11199827765689 / 4000) (280008867686353 / 100000) := by
  exact
    packedTile65536 2800025856 2800156928 14 6056 52915 31 _ _ (271911 / 12500) (2175291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800156928 :
    ThetaLowerSegment 2800156928 2800288000 (280008867686353 / 100000) (17501369285493 / 6250) := by
  exact
    packedTile65536 2800156928 2800288000 14 5995 52916 31 _ _ (2175293 / 100000) (67978 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800288000 :
    ThetaLowerSegment 2800288000 2800419072 (17501369285493 / 6250) (280035075640629 / 100000) := by
  exact
    packedTile65536 2800288000 2800419072 14 6053 52917 31 _ _ (2175297 / 100000) (21753 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800419072 :
    ThetaLowerSegment 2800419072 2800550144 (280035075640629 / 100000)
      (56009620269801 / 20000) := by
  exact
    packedTile65536 2800419072 2800550144 14 5988 52918 31 _ _ (1087651 / 50000) (435061 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800550144 :
    ThetaLowerSegment 2800550144 2800681216 (56009620269801 / 20000) (8751911649024 / 3125) := by
  exact
    packedTile65536 2800550144 2800681216 14 6009 52920 31 _ _ (2175307 / 100000) (217531 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800681216 :
    ThetaLowerSegment 2800681216 2800812288 (8751911649024 / 3125) (140037149297671 / 50000) := by
  exact
    packedTile65536 2800681216 2800812288 14 6034 52921 31 _ _ (2175311 / 100000) (1087657 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800812288 :
    ThetaLowerSegment 2800812288 2800943360 (140037149297671 / 50000)
      (140043668719723 / 50000) := by
  exact
    packedTile65536 2800812288 2800943360 14 5994 52922 31 _ _ (543829 / 25000) (2175319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2800943360 :
    ThetaLowerSegment 2800943360 2801074432 (140043668719723 / 50000)
      (140050216435933 / 50000) := by
  exact
    packedTile65536 2800943360 2801074432 14 6020 52923 31 _ _ (2175321 / 100000) (543831 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801074432 :
    ThetaLowerSegment 2801074432 2801205504 (140050216435933 / 50000)
      (140056733709633 / 50000) := by
  exact
    packedTile65536 2801074432 2801205504 14 5992 52925 31 _ _ (87013 / 4000) (67979 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801205504 :
    ThetaLowerSegment 2801205504 2801336576 (140056733709633 / 50000)
      (140063351063493 / 50000) := by
  exact
    packedTile65536 2801205504 2801336576 14 6084 52926 31 _ _ (217533 / 10000) (2175333 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801336576 :
    ThetaLowerSegment 2801336576 2801467648 (140063351063493 / 50000)
      (280139952092471 / 100000) := by
  exact
    packedTile65536 2801336576 2801467648 14 6091 52927 31 _ _ (435067 / 20000) (1087669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801467648 :
    ThetaLowerSegment 2801467648 2801598720 (280139952092471 / 100000)
      (280153030230539 / 100000) := by
  exact
    packedTile65536 2801467648 2801598720 14 6012 52928 31 _ _ (2175339 / 100000) (1087671 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801598720 :
    ThetaLowerSegment 2801598720 2801729792 (280153030230539 / 100000)
      (280166295478251 / 100000) := by
  exact
    packedTile65536 2801598720 2801729792 14 6098 52930 31 _ _ (135959 / 6250) (2175347 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801729792 :
    ThetaLowerSegment 2801729792 2801860864 (280166295478251 / 100000)
      (280179421534117 / 100000) := by
  exact
    packedTile65536 2801729792 2801860864 14 6034 52931 31 _ _ (2175349 / 100000) (271919 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801860864 :
    ThetaLowerSegment 2801860864 2801991936 (280179421534117 / 100000) (17512027835783 / 6250) := by
  exact
    packedTile65536 2801860864 2801991936 14 5987 52932 31 _ _ (2175353 / 100000) (543839 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2801991936 :
    ThetaLowerSegment 2801991936 2802123008 (17512027835783 / 6250) (140102793355103 / 50000) := by
  exact
    packedTile65536 2801991936 2802123008 14 6041 52933 31 _ _ (1087679 / 50000) (2175361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802123008 :
    ThetaLowerSegment 2802123008 2802254080 (140102793355103 / 50000) (28021874330563 / 10000) := by
  exact
    packedTile65536 2802123008 2802254080 14 6048 52935 31 _ _ (2175363 / 100000) (1087683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802254080 :
    ThetaLowerSegment 2802254080 2802385152 (28021874330563 / 10000)
      (280231884697677 / 100000) := by
  exact
    packedTile65536 2802254080 2802385152 14 6041 52936 31 _ _ (2175367 / 100000) (217537 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802385152 :
    ThetaLowerSegment 2802385152 2802516224 (280231884697677 / 100000)
      (280245015243069 / 100000) := by
  exact
    packedTile65536 2802385152 2802516224 14 6036 52937 31 _ _ (543843 / 25000) (17403 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802516224 :
    ThetaLowerSegment 2802516224 2802647296 (280245015243069 / 100000) (3503228100767 / 1250) := by
  exact
    packedTile65536 2802516224 2802647296 14 6083 52938 31 _ _ (2175377 / 100000) (108769 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802647296 :
    ThetaLowerSegment 2802647296 2802778368 (3503228100767 / 1250) (140135649088989 / 50000) := by
  exact
    packedTile65536 2802647296 2802778368 14 5999 52940 31 _ _ (1087691 / 50000) (435077 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802778368 :
    ThetaLowerSegment 2802778368 2802909440 (140135649088989 / 50000)
      (140142249210113 / 50000) := by
  exact
    packedTile65536 2802778368 2802909440 14 6068 52941 31 _ _ (1087693 / 50000) (2175389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2802909440 :
    ThetaLowerSegment 2802909440 2803040512 (140142249210113 / 50000) (7007442793629 / 2500) := by
  exact
    packedTile65536 2802909440 2803040512 14 6074 52942 31 _ _ (2175391 / 100000) (1087697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803040512 :
    ThetaLowerSegment 2803040512 2803171584 (7007442793629 / 2500) (70077686135649 / 25000) := by
  exact
    packedTile65536 2803040512 2803171584 14 5991 52943 31 _ _ (543849 / 25000) (2175399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803171584 :
    ThetaLowerSegment 2803171584 2803302656 (70077686135649 / 25000) (70080975884299 / 25000) := by
  exact
    packedTile65536 2803171584 2803302656 14 6049 52944 31 _ _ (10877 / 500) (2175403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803302656 :
    ThetaLowerSegment 2803302656 2803433728 (70080975884299 / 25000) (35042148863867 / 12500) := by
  exact
    packedTile65536 2803302656 2803433728 14 6108 52946 31 _ _ (435081 / 20000) (135963 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803433728 :
    ThetaLowerSegment 2803433728 2803564800 (35042148863867 / 12500) (140175131474813 / 50000) := by
  exact
    packedTile65536 2803433728 2803564800 14 6009 52947 31 _ _ (217541 / 10000) (2175413 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803564800 :
    ThetaLowerSegment 2803564800 2803695872 (140175131474813 / 50000) (17522698648909 / 6250) := by
  exact
    packedTile65536 2803564800 2803695872 14 5937 52948 31 _ _ (1087707 / 50000) (2175417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803695872 :
    ThetaLowerSegment 2803695872 2803826944 (17522698648909 / 6250) (56075280550929 / 20000) := by
  exact
    packedTile65536 2803695872 2803826944 14 6079 52949 31 _ _ (2175419 / 100000) (1087711 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803826944 :
    ThetaLowerSegment 2803826944 2803958016 (56075280550929 / 20000)
      (280389577122389 / 100000) := by
  exact
    packedTile65536 2803826944 2803958016 14 6056 52951 31 _ _ (67982 / 3125) (2175427 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2803958016 :
    ThetaLowerSegment 2803958016 2804089088 (280389577122389 / 100000)
      (280402520918989 / 100000) := by
  exact
    packedTile65536 2803958016 2804089088 14 5950 52952 31 _ _ (543857 / 25000) (2175431 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2804089088 :
    ThetaLowerSegment 2804089088 2804220160 (280402520918989 / 100000)
      (70103901537121 / 25000) := by
  exact
    packedTile65536 2804089088 2804220160 14 6015 52953 31 _ _ (2175433 / 100000) (543859 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2804220160 :
    ThetaLowerSegment 2804220160 2804351232 (70103901537121 / 25000) (70107162518683 / 25000) := by
  exact
    packedTile65536 2804220160 2804351232 14 5996 52954 31 _ _ (1087719 / 50000) (2175441 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2804351232 :
    ThetaLowerSegment 2804351232 2804482304 (70107162518683 / 25000) (35055223174191 / 12500) := by
  exact
    packedTile65536 2804351232 2804482304 14 6038 52956 31 _ _ (1087721 / 50000) (435089 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2804482304 :
    ThetaLowerSegment 2804482304 2804613376 (35055223174191 / 12500) (70113720396117 / 25000) := by
  exact
    packedTile65536 2804482304 2804613376 14 6020 52957 31 _ _ (2175447 / 100000) (43509 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2804613376 :
    ThetaLowerSegment 2804613376 2804744448 (70113720396117 / 25000) (70116991188199 / 25000) := by
  exact
    packedTile65536 2804613376 2804744448 14 6014 52958 31 _ _ (543863 / 25000) (435091 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2804744448 :
    ThetaLowerSegment 2804744448 2804875520 (70116991188199 / 25000) (70120295705863 / 25000) := by
  exact
    packedTile65536 2804744448 2804875520 14 6076 52959 31 _ _ (67983 / 3125) (2175459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2804875520 :
    ThetaLowerSegment 2804875520 2805006592 (70120295705863 / 25000)
      (280494259519523 / 100000) := by
  exact
    packedTile65536 2804875520 2805006592 14 6011 52961 31 _ _ (2175461 / 100000) (271933 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805006592 :
    ThetaLowerSegment 2805006592 2805137664 (280494259519523 / 100000)
      (280507412386959 / 100000) := by
  exact
    packedTile65536 2805006592 2805137664 14 6046 52962 31 _ _ (1087733 / 50000) (2175469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805137664 :
    ThetaLowerSegment 2805137664 2805268736 (280507412386959 / 100000)
      (280520386890039 / 100000) := by
  exact
    packedTile65536 2805137664 2805268736 14 5964 52963 31 _ _ (217547 / 10000) (2175473 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805268736 :
    ThetaLowerSegment 2805268736 2805399808 (280520386890039 / 100000)
      (140266803625807 / 50000) := by
  exact
    packedTile65536 2805268736 2805399808 14 6077 52964 31 _ _ (87019 / 4000) (1087739 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805399808 :
    ThetaLowerSegment 2805399808 2805530880 (140266803625807 / 50000)
      (140273332241287 / 50000) := by
  exact
    packedTile65536 2805399808 2805530880 14 6002 52966 31 _ _ (54387 / 2500) (2175483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805530880 :
    ThetaLowerSegment 2805530880 2805661952 (140273332241287 / 50000)
      (140279954414583 / 50000) := by
  exact
    packedTile65536 2805530880 2805661952 14 6088 52967 31 _ _ (543871 / 25000) (2175487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805661952 :
    ThetaLowerSegment 2805661952 2805793024 (140279954414583 / 50000)
      (280573190189511 / 100000) := by
  exact
    packedTile65536 2805661952 2805793024 14 6105 52968 31 _ _ (2175489 / 100000) (543873 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805793024 :
    ThetaLowerSegment 2805793024 2805924096 (280573190189511 / 100000)
      (280586417193031 / 100000) := by
  exact
    packedTile65536 2805793024 2805924096 14 6080 52969 31 _ _ (1087747 / 50000) (2175497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2805924096 :
    ThetaLowerSegment 2805924096 2806055168 (280586417193031 / 100000)
      (280599539796967 / 100000) := by
  exact
    packedTile65536 2805924096 2806055168 14 6032 52970 31 _ _ (1087749 / 50000) (2175501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806055168 :
    ThetaLowerSegment 2806055168 2806186240 (280599539796967 / 100000) (11224506845323 / 4000) := by
  exact
    packedTile65536 2806055168 2806186240 14 6036 52972 31 _ _ (2175503 / 100000) (1087753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806186240 :
    ThetaLowerSegment 2806186240 2806317312 (11224506845323 / 4000) (280625776393267 / 100000) := by
  exact
    packedTile65536 2806186240 2806317312 14 6024 52973 31 _ _ (543877 / 25000) (2175511 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806317312 :
    ThetaLowerSegment 2806317312 2806448384 (280625776393267 / 100000)
      (280639027436859 / 100000) := by
  exact
    packedTile65536 2806317312 2806448384 14 6091 52974 31 _ _ (271939 / 12500) (435103 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806448384 :
    ThetaLowerSegment 2806448384 2806579456 (280639027436859 / 100000)
      (70163040258247 / 25000) := by
  exact
    packedTile65536 2806448384 2806579456 14 6037 52975 31 _ _ (2175517 / 100000) (13597 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806579456 :
    ThetaLowerSegment 2806579456 2806710528 (70163040258247 / 25000) (70166314418857 / 25000) := by
  exact
    packedTile65536 2806579456 2806710528 14 6020 52977 31 _ _ (1087761 / 50000) (87021 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806710528 :
    ThetaLowerSegment 2806710528 2806841600 (70166314418857 / 25000) (70169527670759 / 25000) := by
  exact
    packedTile65536 2806710528 2806841600 14 5908 52978 31 _ _ (1087763 / 50000) (2175529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806841600 :
    ThetaLowerSegment 2806841600 2806972672 (70169527670759 / 25000) (140345584110049 / 50000) := by
  exact
    packedTile65536 2806841600 2806972672 14 6002 52979 31 _ _ (2175531 / 100000) (1087767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2806972672 :
    ThetaLowerSegment 2806972672 2807103744 (140345584110049 / 50000)
      (140352073733937 / 50000) := by
  exact
    packedTile65536 2806972672 2807103744 14 5966 52980 31 _ _ (135971 / 6250) (2175539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2807103744 :
    ThetaLowerSegment 2807103744 2807234816 (140352073733937 / 50000)
      (140358624284877 / 50000) := by
  exact
    packedTile65536 2807103744 2807234816 14 6022 52982 31 _ _ (108777 / 5000) (2175543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2807234816 :
    ThetaLowerSegment 2807234816 2807365888 (140358624284877 / 50000)
      (140365220537317 / 50000) := by
  exact
    packedTile65536 2807234816 2807365888 14 6064 52983 31 _ _ (435109 / 20000) (543887 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2807365888 :
    ThetaLowerSegment 2807365888 2807496960 (140365220537317 / 50000)
      (140371775469467 / 50000) := by
  exact
    packedTile65536 2807365888 2807496960 14 6026 52984 31 _ _ (43511 / 2000) (2175553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2807496960 :
    ThetaLowerSegment 2807496960 2807628032 (140371775469467 / 50000)
      (140378326062561 / 50000) := by
  exact
    packedTile65536 2807496960 2807628032 14 6022 52985 31 _ _ (1087777 / 50000) (2175557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2807628032 :
    ThetaLowerSegment 2807628032 2807759104 (140378326062561 / 50000)
      (280769768570333 / 100000) := by
  exact
    packedTile65536 2807628032 2807759104 14 6029 52987 31 _ _ (2175559 / 100000) (1087781 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2807759104 :
    ThetaLowerSegment 2807759104 2807890176 (280769768570333 / 100000)
      (280782761038541 / 100000) := by
  exact
    packedTile65536 2807759104 2807890176 14 5972 52988 31 _ _ (543891 / 25000) (2175567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2807890176 :
    ThetaLowerSegment 2807890176 2808021248 (280782761038541 / 100000)
      (280795797041997 / 100000) := by
  exact
    packedTile65536 2807890176 2808021248 14 5992 52989 31 _ _ (135973 / 6250) (2175571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808021248 :
    ThetaLowerSegment 2808021248 2808152320 (280795797041997 / 100000)
      (280808967960939 / 100000) := by
  exact
    packedTile65536 2808021248 2808152320 14 6054 52990 31 _ _ (2175573 / 100000) (271947 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808152320 :
    ThetaLowerSegment 2808152320 2808283392 (280808967960939 / 100000)
      (280822064940499 / 100000) := by
  exact
    packedTile65536 2808152320 2808283392 14 6020 52992 31 _ _ (1087789 / 50000) (2175581 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808283392 :
    ThetaLowerSegment 2808283392 2808414464 (280822064940499 / 100000)
      (280835170646467 / 100000) := by
  exact
    packedTile65536 2808283392 2808414464 14 6024 52993 31 _ _ (1087791 / 50000) (435117 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808414464 :
    ThetaLowerSegment 2808414464 2808545536 (280835170646467 / 100000)
      (280848150198509 / 100000) := by
  exact
    packedTile65536 2808414464 2808545536 14 5966 52994 31 _ _ (2175587 / 100000) (217559 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808545536 :
    ThetaLowerSegment 2808545536 2808676608 (280848150198509 / 100000)
      (56172274689337 / 20000) := by
  exact
    packedTile65536 2808545536 2808676608 14 6078 52995 31 _ _ (271949 / 12500) (435119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808676608 :
    ThetaLowerSegment 2808676608 2808807680 (56172274689337 / 20000)
      (280874540153677 / 100000) := by
  exact
    packedTile65536 2808676608 2808807680 14 6052 52996 31 _ _ (543899 / 25000) (2175599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808807680 :
    ThetaLowerSegment 2808807680 2808938752 (280874540153677 / 100000)
      (280887519789243 / 100000) := by
  exact
    packedTile65536 2808807680 2808938752 14 5966 52998 31 _ _ (2175601 / 100000) (543901 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2808938752 :
    ThetaLowerSegment 2808938752 2809069824 (280887519789243 / 100000)
      (56180122082109 / 20000) := by
  exact
    packedTile65536 2808938752 2809069824 14 6017 52999 31 _ _ (1087803 / 50000) (2175609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809069824 :
    ThetaLowerSegment 2809069824 2809200896 (56180122082109 / 20000) (11236547694139 / 4000) := by
  exact
    packedTile65536 2809069824 2809200896 14 6013 53000 31 _ _ (217561 / 10000) (2175613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809200896 :
    ThetaLowerSegment 2809200896 2809331968 (11236547694139 / 4000) (56185352689679 / 20000) := by
  exact
    packedTile65536 2809200896 2809331968 14 6008 53001 31 _ _ (435123 / 20000) (1087809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809331968 :
    ThetaLowerSegment 2809331968 2809463040 (56185352689679 / 20000) (56187983014259 / 20000) := by
  exact
    packedTile65536 2809331968 2809463040 14 6045 53003 31 _ _ (108781 / 5000) (2175623 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809463040 :
    ThetaLowerSegment 2809463040 2809594112 (56187983014259 / 20000) (56190619870547 / 20000) := by
  exact
    packedTile65536 2809463040 2809594112 14 6060 53004 31 _ _ (271953 / 12500) (2175627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809594112 :
    ThetaLowerSegment 2809594112 2809725184 (56190619870547 / 20000) (35120777027497 / 12500) := by
  exact
    packedTile65536 2809594112 2809725184 14 6029 53005 31 _ _ (2175629 / 100000) (135977 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809725184 :
    ThetaLowerSegment 2809725184 2809856256 (35120777027497 / 12500) (35122417455533 / 12500) := by
  exact
    packedTile65536 2809725184 2809856256 14 6032 53006 31 _ _ (1087817 / 50000) (2175637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809856256 :
    ThetaLowerSegment 2809856256 2809987328 (35122417455533 / 12500) (140496271795643 / 50000) := by
  exact
    packedTile65536 2809856256 2809987328 14 6069 53008 31 _ _ (1087819 / 50000) (2175641 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2809987328 :
    ThetaLowerSegment 2809987328 2810118400 (140496271795643 / 50000)
      (140502781319499 / 50000) := by
  exact
    packedTile65536 2809987328 2810118400 14 5984 53009 31 _ _ (2175643 / 100000) (1087823 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2810118400 :
    ThetaLowerSegment 2810118400 2810249472 (140502781319499 / 50000)
      (140509326756507 / 50000) := by
  exact
    packedTile65536 2810118400 2810249472 14 6017 53010 31 _ _ (67989 / 3125) (2175651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2810249472 :
    ThetaLowerSegment 2810249472 2810380544 (140509326756507 / 50000)
      (140515860239463 / 50000) := by
  exact
    packedTile65536 2810249472 2810380544 14 6006 53011 31 _ _ (543913 / 25000) (435131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2810380544 :
    ThetaLowerSegment 2810380544 2810511616 (140515860239463 / 50000)
      (140522374156521 / 50000) := by
  exact
    packedTile65536 2810380544 2810511616 14 5988 53013 31 _ _ (2175657 / 100000) (108783 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2810511616 :
    ThetaLowerSegment 2810511616 2810642688 (140522374156521 / 50000) (14052890005469 / 5000) := by
  exact
    packedTile65536 2810511616 2810642688 14 5999 53014 31 _ _ (1087831 / 50000) (435133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2810642688 :
    ThetaLowerSegment 2810642688 2810773760 (14052890005469 / 5000) (8783459703482 / 3125) := by
  exact
    packedTile65536 2810642688 2810773760 14 5934 53015 31 _ _ (1087833 / 50000) (2175669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2810773760 :
    ThetaLowerSegment 2810773760 2810904832 (8783459703482 / 3125) (281084032144957 / 100000) := by
  exact
    packedTile65536 2810773760 2810904832 14 6123 53016 31 _ _ (2175671 / 100000) (1087837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2810904832 :
    ThetaLowerSegment 2810904832 2811035904 (281084032144957 / 100000)
      (281097134065829 / 100000) := by
  exact
    packedTile65536 2810904832 2811035904 14 6022 53017 31 _ _ (543919 / 25000) (2175679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811035904 :
    ThetaLowerSegment 2811035904 2811166976 (281097134065829 / 100000)
      (281110168564709 / 100000) := by
  exact
    packedTile65536 2811035904 2811166976 14 5991 53019 31 _ _ (13598 / 625) (2175683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811166976 :
    ThetaLowerSegment 2811166976 2811298048 (281110168564709 / 100000) (8785101728437 / 3125) := by
  exact
    packedTile65536 2811166976 2811298048 14 6015 53020 31 _ _ (435137 / 20000) (271961 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811298048 :
    ThetaLowerSegment 2811298048 2811429120 (8785101728437 / 3125) (70284065396201 / 25000) := by
  exact
    packedTile65536 2811298048 2811429120 14 5978 53021 31 _ _ (217569 / 10000) (2175693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811429120 :
    ThetaLowerSegment 2811429120 2811560192 (70284065396201 / 25000) (140574650259473 / 50000) := by
  exact
    packedTile65536 2811429120 2811560192 14 5993 53022 31 _ _ (1087847 / 50000) (2175697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811560192 :
    ThetaLowerSegment 2811560192 2811691264 (140574650259473 / 50000) (35145286180247 / 12500) := by
  exact
    packedTile65536 2811560192 2811691264 14 5970 53024 31 _ _ (2175699 / 100000) (1087851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811691264 :
    ThetaLowerSegment 2811691264 2811822336 (35145286180247 / 12500) (35146920677877 / 12500) := by
  exact
    packedTile65536 2811691264 2811822336 14 6010 53025 31 _ _ (271963 / 12500) (2175707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811822336 :
    ThetaLowerSegment 2811822336 2811953408 (35146920677877 / 12500) (14059433276301 / 5000) := by
  exact
    packedTile65536 2811822336 2811953408 14 6113 53026 31 _ _ (543927 / 25000) (2175711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2811953408 :
    ThetaLowerSegment 2811953408 2812084480 (14059433276301 / 5000) (11248067486733 / 4000) := by
  exact
    packedTile65536 2811953408 2812084480 14 5985 53027 31 _ _ (2175713 / 100000) (543929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2812084480 :
    ThetaLowerSegment 2812084480 2812215552 (11248067486733 / 4000) (281214906830893 / 100000) := by
  exact
    packedTile65536 2812084480 2812215552 14 6076 53029 31 _ _ (1087859 / 50000) (2175721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2812215552 :
    ThetaLowerSegment 2812215552 2812346624 (281214906830893 / 100000)
      (281227895891233 / 100000) := by
  exact
    packedTile65536 2812215552 2812346624 14 5970 53030 31 _ _ (1087861 / 50000) (87029 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2812346624 :
    ThetaLowerSegment 2812346624 2812477696 (281227895891233 / 100000)
      (70310257688783 / 25000) := by
  exact
    packedTile65536 2812346624 2812477696 14 6037 53031 31 _ _ (2175727 / 100000) (217573 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2812477696 :
    ThetaLowerSegment 2812477696 2812608768 (70310257688783 / 25000) (70313564801423 / 25000) := by
  exact
    packedTile65536 2812477696 2812608768 14 6080 53032 31 _ _ (543933 / 25000) (435147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2812608768 :
    ThetaLowerSegment 2812608768 2812739840 (70313564801423 / 25000) (70316878447351 / 25000) := by
  exact
    packedTile65536 2812608768 2812739840 14 6092 53034 31 _ _ (271967 / 12500) (2175739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2812739840 :
    ThetaLowerSegment 2812739840 2812870912 (70316878447351 / 25000)
      (281280422460757 / 100000) := by
  exact
    packedTile65536 2812739840 2812870912 14 5933 53035 31 _ _ (2175741 / 100000) (67992 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2812870912 :
    ThetaLowerSegment 2812870912 2813001984 (281280422460757 / 100000)
      (281293492166979 / 100000) := by
  exact
    packedTile65536 2812870912 2813001984 14 6007 53036 31 _ _ (1087873 / 50000) (2175749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813001984 :
    ThetaLowerSegment 2813001984 2813133056 (281293492166979 / 100000)
      (281306616290979 / 100000) := by
  exact
    packedTile65536 2813001984 2813133056 14 6032 53037 31 _ _ (8703 / 400) (2175753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813133056 :
    ThetaLowerSegment 2813133056 2813264128 (281306616290979 / 100000)
      (140659906122527 / 50000) := by
  exact
    packedTile65536 2813133056 2813264128 14 6065 53038 31 _ _ (435151 / 20000) (1087879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813264128 :
    ThetaLowerSegment 2813264128 2813395200 (140659906122527 / 50000)
      (140666483445007 / 50000) := by
  exact
    packedTile65536 2813264128 2813395200 14 6046 53040 31 _ _ (27197 / 1250) (2175763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813395200 :
    ThetaLowerSegment 2813395200 2813526272 (140666483445007 / 50000)
      (140672974836901 / 50000) := by
  exact
    packedTile65536 2813395200 2813526272 14 5967 53041 31 _ _ (543941 / 25000) (2175767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813526272 :
    ThetaLowerSegment 2813526272 2813657344 (140672974836901 / 50000) (17584934232363 / 6250) := by
  exact
    packedTile65536 2813526272 2813657344 14 5974 53042 31 _ _ (2175769 / 100000) (543943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813657344 :
    ThetaLowerSegment 2813657344 2813788416 (17584934232363 / 6250) (35171510086209 / 12500) := by
  exact
    packedTile65536 2813657344 2813788416 14 6036 53043 31 _ _ (1087887 / 50000) (2175777 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813788416 :
    ThetaLowerSegment 2813788416 2813919488 (35171510086209 / 12500) (140692570942503 / 50000) := by
  exact
    packedTile65536 2813788416 2813919488 14 6003 53045 31 _ _ (1087889 / 50000) (2175781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2813919488 :
    ThetaLowerSegment 2813919488 2814050560 (140692570942503 / 50000)
      (281398272735411 / 100000) := by
  exact
    packedTile65536 2813919488 2814050560 14 6035 53046 31 _ _ (2175783 / 100000) (1087893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814050560 :
    ThetaLowerSegment 2814050560 2814181632 (281398272735411 / 100000)
      (281411429725447 / 100000) := by
  exact
    packedTile65536 2814050560 2814181632 14 6047 53047 31 _ _ (543947 / 25000) (2175791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814181632 :
    ThetaLowerSegment 2814181632 2814312704 (281411429725447 / 100000)
      (281424530169079 / 100000) := by
  exact
    packedTile65536 2814181632 2814312704 14 6021 53048 31 _ _ (135987 / 6250) (435159 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814312704 :
    ThetaLowerSegment 2814312704 2814443776 (281424530169079 / 100000)
      (140718826200393 / 50000) := by
  exact
    packedTile65536 2814312704 2814443776 14 6031 53050 31 _ _ (2175797 / 100000) (10879 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814443776 :
    ThetaLowerSegment 2814443776 2814574848 (140718826200393 / 50000) (28145095090261 / 10000) := by
  exact
    packedTile65536 2814443776 2814574848 14 6112 53051 31 _ _ (1087901 / 50000) (435161 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814574848 :
    ThetaLowerSegment 2814574848 2814705920 (28145095090261 / 10000) (140731996341887 / 50000) := by
  exact
    packedTile65536 2814574848 2814705920 14 5994 53052 31 _ _ (1087903 / 50000) (2175809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814705920 :
    ThetaLowerSegment 2814705920 2814836992 (140731996341887 / 50000)
      (140738654323547 / 50000) := by
  exact
    packedTile65536 2814705920 2814836992 14 6120 53053 31 _ _ (2175811 / 100000) (1087907 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814836992 :
    ThetaLowerSegment 2814836992 2814968064 (140738654323547 / 50000) (28149048538879 / 10000) := by
  exact
    packedTile65536 2814836992 2814968064 14 6056 53055 31 _ _ (271977 / 12500) (2175819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2814968064 :
    ThetaLowerSegment 2814968064 2815099136 (28149048538879 / 10000) (28150341411123 / 10000) := by
  exact
    packedTile65536 2814968064 2815099136 14 5942 53056 31 _ _ (108791 / 5000) (2175823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815099136 :
    ThetaLowerSegment 2815099136 2815230208 (28150341411123 / 10000) (14075827587129 / 5000) := by
  exact
    packedTile65536 2815099136 2815230208 14 6038 53057 31 _ _ (87033 / 4000) (543957 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815230208 :
    ThetaLowerSegment 2815230208 2815361280 (14075827587129 / 5000) (140764853402357 / 50000) := by
  exact
    packedTile65536 2815230208 2815361280 14 6046 53058 31 _ _ (2175829 / 100000) (271979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815361280 :
    ThetaLowerSegment 2815361280 2815492352 (140764853402357 / 50000) (35192854745363 / 12500) := by
  exact
    packedTile65536 2815361280 2815492352 14 6035 53059 31 _ _ (1087917 / 50000) (2175837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815492352 :
    ThetaLowerSegment 2815492352 2815623424 (35192854745363 / 12500) (56311221680993 / 20000) := by
  exact
    packedTile65536 2815492352 2815623424 14 6099 53061 31 _ _ (2175839 / 100000) (1087921 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815623424 :
    ThetaLowerSegment 2815623424 2815754496 (56311221680993 / 20000)
      (281569189573081 / 100000) := by
  exact
    packedTile65536 2815623424 2815754496 14 6012 53062 31 _ _ (2175843 / 100000) (1087923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815754496 :
    ThetaLowerSegment 2815754496 2815885568 (281569189573081 / 100000)
      (281582281650497 / 100000) := by
  exact
    packedTile65536 2815754496 2815885568 14 6017 53063 31 _ _ (271981 / 12500) (2175851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2815885568 :
    ThetaLowerSegment 2815885568 2816016640 (281582281650497 / 100000)
      (140797678175587 / 50000) := by
  exact
    packedTile65536 2815885568 2816016640 14 6009 53064 31 _ _ (2175853 / 100000) (135991 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816016640 :
    ThetaLowerSegment 2816016640 2816147712 (140797678175587 / 50000)
      (281608313579609 / 100000) := by
  exact
    packedTile65536 2816016640 2816147712 14 5955 53066 31 _ _ (2175857 / 100000) (108793 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816147712 :
    ThetaLowerSegment 2816147712 2816278784 (281608313579609 / 100000)
      (281621383982643 / 100000) := by
  exact
    packedTile65536 2816147712 2816278784 14 6007 53067 31 _ _ (1087931 / 50000) (435173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816278784 :
    ThetaLowerSegment 2816278784 2816409856 (281621383982643 / 100000)
      (281634565384929 / 100000) := by
  exact
    packedTile65536 2816278784 2816409856 14 6058 53068 31 _ _ (2175867 / 100000) (217587 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816409856 :
    ThetaLowerSegment 2816409856 2816540928 (281634565384929 / 100000)
      (140823826624497 / 50000) := by
  exact
    packedTile65536 2816409856 2816540928 14 6015 53069 31 _ _ (2175871 / 100000) (1087937 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816540928 :
    ThetaLowerSegment 2816540928 2816672000 (140823826624497 / 50000)
      (140830337933427 / 50000) := by
  exact
    packedTile65536 2816540928 2816672000 14 5985 53071 31 _ _ (543969 / 25000) (2175879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816672000 :
    ThetaLowerSegment 2816672000 2816803072 (140830337933427 / 50000) (70418418644987 / 25000) := by
  exact
    packedTile65536 2816672000 2816803072 14 5974 53072 31 _ _ (2175881 / 100000) (543971 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816803072 :
    ThetaLowerSegment 2816803072 2816934144 (70418418644987 / 25000) (140843371472629 / 50000) := by
  exact
    packedTile65536 2816803072 2816934144 14 6006 53073 31 _ _ (435177 / 20000) (135993 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2816934144 :
    ThetaLowerSegment 2816934144 2817065216 (140843371472629 / 50000)
      (140849949188099 / 50000) := by
  exact
    packedTile65536 2816934144 2817065216 14 6046 53074 31 _ _ (217589 / 10000) (2175893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817065216 :
    ThetaLowerSegment 2817065216 2817196288 (140849949188099 / 50000)
      (281713051661473 / 100000) := by
  exact
    packedTile65536 2817065216 2817196288 14 6045 53076 31 _ _ (435179 / 20000) (1087949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817196288 :
    ThetaLowerSegment 2817196288 2817327360 (281713051661473 / 100000)
      (281725967797937 / 100000) := by
  exact
    packedTile65536 2817196288 2817327360 14 5936 53077 31 _ _ (2175899 / 100000) (1087951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817327360 :
    ThetaLowerSegment 2817327360 2817458432 (281725967797937 / 100000)
      (56347816394269 / 20000) := by
  exact
    packedTile65536 2817327360 2817458432 14 6027 53078 31 _ _ (67997 / 3125) (2175907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817458432 :
    ThetaLowerSegment 2817458432 2817589504 (56347816394269 / 20000)
      (281752263628067 / 100000) := by
  exact
    packedTile65536 2817458432 2817589504 14 6058 53079 31 _ _ (2175909 / 100000) (271989 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817589504 :
    ThetaLowerSegment 2817589504 2817720576 (281752263628067 / 100000)
      (70441356431451 / 25000) := by
  exact
    packedTile65536 2817589504 2817720576 14 6049 53080 31 _ _ (2175913 / 100000) (543979 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817720576 :
    ThetaLowerSegment 2817720576 2817851648 (70441356431451 / 25000) (70444657299057 / 25000) := by
  exact
    packedTile65536 2817720576 2817851648 14 6068 53082 31 _ _ (1087959 / 50000) (2175921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817851648 :
    ThetaLowerSegment 2817851648 2817982720 (70444657299057 / 25000) (56358380030121 / 20000) := by
  exact
    packedTile65536 2817851648 2817982720 14 6099 53083 31 _ _ (2175923 / 100000) (1087963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2817982720 :
    ThetaLowerSegment 2817982720 2818113792 (56358380030121 / 20000) (35225627351811 / 12500) := by
  exact
    packedTile65536 2817982720 2818113792 14 6029 53084 31 _ _ (2175927 / 100000) (217593 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2818113792 :
    ThetaLowerSegment 2818113792 2818244864 (35225627351811 / 12500) (7045451642569 / 2500) := by
  exact
    packedTile65536 2818113792 2818244864 14 5996 53085 31 _ _ (543983 / 25000) (435187 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2818244864 :
    ThetaLowerSegment 2818244864 2818375936 (7045451642569 / 2500) (140915554134569 / 50000) := by
  exact
    packedTile65536 2818244864 2818375936 14 5994 53087 31 _ _ (2175937 / 100000) (108797 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2818375936 :
    ThetaLowerSegment 2818375936 2818507008 (140915554134569 / 50000)
      (281844300999421 / 100000) := by
  exact
    packedTile65536 2818375936 2818507008 14 6063 53088 31 _ _ (2175941 / 100000) (271993 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2818507008 :
    ThetaLowerSegment 2818507008 2818638080 (281844300999421 / 100000)
      (281857580797859 / 100000) := by
  exact
    packedTile65536 2818507008 2818638080 14 6103 53089 31 _ _ (1087973 / 50000) (2175949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2818638080 :
    ThetaLowerSegment 2818638080 2818769152 (281857580797859 / 100000)
      (281870760527009 / 100000) := by
  exact
    packedTile65536 2818638080 2818769152 14 6057 53090 31 _ _ (43519 / 2000) (2175953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2818769152 :
    ThetaLowerSegment 2818769152 2818900224 (281870760527009 / 100000)
      (281883903295209 / 100000) := by
  exact
    packedTile65536 2818769152 2818900224 14 6040 53092 31 _ _ (435191 / 20000) (1087979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2818900224 :
    ThetaLowerSegment 2818900224 2819031296 (281883903295209 / 100000)
      (281897065677249 / 100000) := by
  exact
    packedTile65536 2818900224 2819031296 14 6049 53093 31 _ _ (54399 / 2500) (2175963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819031296 :
    ThetaLowerSegment 2819031296 2819162368 (281897065677249 / 100000)
      (281910036598653 / 100000) := by
  exact
    packedTile65536 2819031296 2819162368 14 5961 53094 31 _ _ (543991 / 25000) (2175967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819162368 :
    ThetaLowerSegment 2819162368 2819293440 (281910036598653 / 100000)
      (281923257786297 / 100000) := by
  exact
    packedTile65536 2819162368 2819293440 14 6076 53095 31 _ _ (2175969 / 100000) (543993 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819293440 :
    ThetaLowerSegment 2819293440 2819424512 (281923257786297 / 100000)
      (281936468124451 / 100000) := by
  exact
    packedTile65536 2819293440 2819424512 14 6071 53097 31 _ _ (1087987 / 50000) (2175977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819424512 :
    ThetaLowerSegment 2819424512 2819555584 (281936468124451 / 100000)
      (281949576215923 / 100000) := by
  exact
    packedTile65536 2819424512 2819555584 14 6024 53098 31 _ _ (1087989 / 50000) (2175981 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819555584 :
    ThetaLowerSegment 2819555584 2819686656 (281949576215923 / 100000) (8811331369567 / 3125) := by
  exact
    packedTile65536 2819555584 2819686656 14 5987 53099 31 _ _ (2175983 / 100000) (1087993 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819686656 :
    ThetaLowerSegment 2819686656 2819817728 (8811331369567 / 3125) (3524693897337 / 1250) := by
  exact
    packedTile65536 2819686656 2819817728 14 5932 53100 31 _ _ (543997 / 25000) (2175991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819817728 :
    ThetaLowerSegment 2819817728 2819948800 (3524693897337 / 1250) (8812147773824 / 3125) := by
  exact
    packedTile65536 2819817728 2819948800 14 6074 53101 31 _ _ (271999 / 12500) (435199 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2819948800 :
    ThetaLowerSegment 2819948800 2820079872 (8812147773824 / 3125) (282001943592149 / 100000) := by
  exact
    packedTile65536 2819948800 2820079872 14 6073 53103 31 _ _ (2175997 / 100000) (544 / 25)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820079872 :
    ThetaLowerSegment 2820079872 2820210944 (282001943592149 / 100000)
      (282014977844129 / 100000) := by
  exact
    packedTile65536 2820079872 2820210944 14 5990 53104 31 _ _ (1088001 / 50000) (435201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820210944 :
    ThetaLowerSegment 2820210944 2820342016 (282014977844129 / 100000)
      (282028284120819 / 100000) := by
  exact
    packedTile65536 2820210944 2820342016 14 6115 53105 31 _ _ (1088003 / 50000) (2176009 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820342016 :
    ThetaLowerSegment 2820342016 2820473088 (282028284120819 / 100000)
      (282041257498401 / 100000) := by
  exact
    packedTile65536 2820342016 2820473088 14 5962 53106 31 _ _ (2176011 / 100000) (1088007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820473088 :
    ThetaLowerSegment 2820473088 2820604160 (282041257498401 / 100000)
      (282054548604129 / 100000) := by
  exact
    packedTile65536 2820473088 2820604160 14 6108 53108 31 _ _ (136001 / 6250) (2176019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820604160 :
    ThetaLowerSegment 2820604160 2820735232 (282054548604129 / 100000)
      (282067535091489 / 100000) := by
  exact
    packedTile65536 2820604160 2820735232 14 5968 53109 31 _ _ (108801 / 5000) (2176023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820735232 :
    ThetaLowerSegment 2820735232 2820866304 (282067535091489 / 100000)
      (70520162498541 / 25000) := by
  exact
    packedTile65536 2820735232 2820866304 14 6027 53110 31 _ _ (87041 / 4000) (544007 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820866304 :
    ThetaLowerSegment 2820866304 2820997376 (70520162498541 / 25000)
      (282093734456541 / 100000) := by
  exact
    packedTile65536 2820866304 2820997376 14 6013 53111 31 _ _ (2176029 / 100000) (68001 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2820997376 :
    ThetaLowerSegment 2820997376 2821128448 (282093734456541 / 100000)
      (282106899462241 / 100000) := by
  exact
    packedTile65536 2820997376 2821128448 14 6050 53113 31 _ _ (1088017 / 50000) (2176037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2821128448 :
    ThetaLowerSegment 2821128448 2821259520 (282106899462241 / 100000)
      (70530009052421 / 25000) := by
  exact
    packedTile65536 2821128448 2821259520 14 6037 53114 31 _ _ (2176039 / 100000) (1088021 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2821259520 :
    ThetaLowerSegment 2821259520 2821390592 (70530009052421 / 25000) (141066626747433 / 50000) := by
  exact
    packedTile65536 2821259520 2821390592 14 6074 53115 31 _ _ (2176043 / 100000) (1088023 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2821390592 :
    ThetaLowerSegment 2821390592 2821521664 (141066626747433 / 50000)
      (141073184268081 / 50000) := by
  exact
    packedTile65536 2821390592 2821521664 14 6027 53116 31 _ _ (136003 / 6250) (2176051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2821521664 :
    ThetaLowerSegment 2821521664 2821652736 (141073184268081 / 50000) (7053979419603 / 2500) := by
  exact
    packedTile65536 2821521664 2821652736 14 5886 53117 31 _ _ (2176053 / 100000) (272007 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2821652736 :
    ThetaLowerSegment 2821652736 2821783808 (7053979419603 / 2500) (141086210133511 / 50000) := by
  exact
    packedTile65536 2821652736 2821783808 14 6086 53119 31 _ _ (2176057 / 100000) (108803 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2821783808 :
    ThetaLowerSegment 2821783808 2821914880 (141086210133511 / 50000) (35273202804397 / 12500) := by
  exact
    packedTile65536 2821783808 2821914880 14 6067 53120 31 _ _ (1088031 / 50000) (435213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2821914880 :
    ThetaLowerSegment 2821914880 2822045952 (35273202804397 / 12500)
      (282198685365377 / 100000) := by
  exact
    packedTile65536 2821914880 2822045952 14 6003 53121 31 _ _ (2176067 / 100000) (217607 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822045952 :
    ThetaLowerSegment 2822045952 2822177024 (282198685365377 / 100000)
      (282211811425649 / 100000) := by
  exact
    packedTile65536 2822045952 2822177024 14 6032 53122 31 _ _ (2176071 / 100000) (1088037 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822177024 :
    ThetaLowerSegment 2822177024 2822308096 (282211811425649 / 100000)
      (282224907051017 / 100000) := by
  exact
    packedTile65536 2822177024 2822308096 14 6018 53124 31 _ _ (544019 / 25000) (2176079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822308096 :
    ThetaLowerSegment 2822308096 2822439168 (282224907051017 / 100000)
      (141119000265197 / 50000) := by
  exact
    packedTile65536 2822308096 2822439168 14 6017 53125 31 _ _ (2176081 / 100000) (544021 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822439168 :
    ThetaLowerSegment 2822439168 2822570240 (141119000265197 / 50000)
      (141125624267937 / 50000) := by
  exact
    packedTile65536 2822439168 2822570240 14 6088 53126 31 _ _ (435217 / 20000) (272011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822570240 :
    ThetaLowerSegment 2822570240 2822701312 (141125624267937 / 50000)
      (141132233053267 / 50000) := by
  exact
    packedTile65536 2822570240 2822701312 14 6074 53127 31 _ _ (217609 / 10000) (2176093 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822701312 :
    ThetaLowerSegment 2822701312 2822832384 (141132233053267 / 50000) (70569368700611 / 25000) := by
  exact
    packedTile65536 2822701312 2822832384 14 5978 53129 31 _ _ (435219 / 20000) (1088049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822832384 :
    ThetaLowerSegment 2822832384 2822963456 (70569368700611 / 25000)
      (282290698956067 / 100000) := by
  exact
    packedTile65536 2822832384 2822963456 14 6077 53130 31 _ _ (2176099 / 100000) (1088051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2822963456 :
    ThetaLowerSegment 2822963456 2823094528 (282290698956067 / 100000)
      (56460788980223 / 20000) := by
  exact
    packedTile65536 2822963456 2823094528 14 6087 53131 31 _ _ (272013 / 12500) (2176107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823094528 :
    ThetaLowerSegment 2823094528 2823225600 (56460788980223 / 20000) (56463404662039 / 20000) := by
  exact
    packedTile65536 2823094528 2823225600 14 6010 53132 31 _ _ (544027 / 25000) (2176111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823225600 :
    ThetaLowerSegment 2823225600 2823356672 (56463404662039 / 20000) (14116498015099 / 5000) := by
  exact
    packedTile65536 2823225600 2823356672 14 5945 53134 31 _ _ (2176113 / 100000) (544029 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823356672 :
    ThetaLowerSegment 2823356672 2823487744 (14116498015099 / 5000) (70585756428613 / 25000) := by
  exact
    packedTile65536 2823356672 2823487744 14 6004 53135 31 _ _ (1088059 / 50000) (2176121 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823487744 :
    ThetaLowerSegment 2823487744 2823618816 (70585756428613 / 25000) (14117808909791 / 5000) := by
  exact
    packedTile65536 2823487744 2823618816 14 6044 53136 31 _ _ (1088061 / 50000) (17409 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823618816 :
    ThetaLowerSegment 2823618816 2823749888 (14117808909791 / 5000) (8824047024924 / 3125) := by
  exact
    packedTile65536 2823618816 2823749888 14 6124 53137 31 _ _ (2176127 / 100000) (217613 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823749888 :
    ThetaLowerSegment 2823749888 2823880960 (8824047024924 / 3125) (17648912819513 / 6250) := by
  exact
    packedTile65536 2823749888 2823880960 14 6020 53138 31 _ _ (544033 / 25000) (435227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2823880960 :
    ThetaLowerSegment 2823880960 2824012032 (17648912819513 / 6250) (35299469981791 / 12500) := by
  exact
    packedTile65536 2823880960 2824012032 14 6045 53140 31 _ _ (272017 / 12500) (2176139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824012032 :
    ThetaLowerSegment 2824012032 2824143104 (35299469981791 / 12500)
      (282408805819623 / 100000) := by
  exact
    packedTile65536 2824012032 2824143104 14 5995 53141 31 _ _ (2176141 / 100000) (136009 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824143104 :
    ThetaLowerSegment 2824143104 2824274176 (282408805819623 / 100000)
      (282421869224061 / 100000) := by
  exact
    packedTile65536 2824143104 2824274176 14 6003 53142 31 _ _ (1088073 / 50000) (2176149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824274176 :
    ThetaLowerSegment 2824274176 2824405248 (282421869224061 / 100000)
      (282434963118611 / 100000) := by
  exact
    packedTile65536 2824274176 2824405248 14 6017 53143 31 _ _ (43523 / 2000) (2176153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824405248 :
    ThetaLowerSegment 2824405248 2824536320 (282434963118611 / 100000)
      (282448259425661 / 100000) := by
  exact
    packedTile65536 2824405248 2824536320 14 6110 53145 31 _ _ (435231 / 20000) (1088079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824536320 :
    ThetaLowerSegment 2824536320 2824667392 (282448259425661 / 100000)
      (282461318561821 / 100000) := by
  exact
    packedTile65536 2824536320 2824667392 14 6001 53146 31 _ _ (13601 / 625) (2176163 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824667392 :
    ThetaLowerSegment 2824667392 2824798464 (282461318561821 / 100000)
      (282474408188281 / 100000) := by
  exact
    packedTile65536 2824667392 2824798464 14 6015 53147 31 _ _ (544041 / 25000) (2176167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824798464 :
    ThetaLowerSegment 2824798464 2824929536 (282474408188281 / 100000)
      (70621824409317 / 25000) := by
  exact
    packedTile65536 2824798464 2824929536 14 5923 53148 31 _ _ (2176169 / 100000) (544043 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2824929536 :
    ThetaLowerSegment 2824929536 2825060608 (70621824409317 / 25000) (56500070499819 / 20000) := by
  exact
    packedTile65536 2824929536 2825060608 14 5999 53150 31 _ _ (2176173 / 100000) (136011 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825060608 :
    ThetaLowerSegment 2825060608 2825191680 (56500070499819 / 20000)
      (282513531433063 / 100000) := by
  exact
    packedTile65536 2825060608 2825191680 14 6056 53151 31 _ _ (1088089 / 50000) (2176181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825191680 :
    ThetaLowerSegment 2825191680 2825322752 (282513531433063 / 100000)
      (35315821118177 / 12500) := by
  exact
    packedTile65536 2825191680 2825322752 14 5991 53152 31 _ _ (2176183 / 100000) (1088093 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825322752 :
    ThetaLowerSegment 2825322752 2825339136 (35315821118177 / 12500)
      (282528225023723 / 100000) := by
  exact
    packedTile65536 2825322752 2825339136 11 761 53153 31 _ _ (2176187 / 100000) (217619 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2825339136 :
    ThetaLowerSegment 2825339136 2825341184 (282528225023723 / 100000)
      (282528446994899 / 100000) := by
  exact
    packedTile65536 2825339136 2825341184 8 102 53153 31 _ _ (544047 / 25000) (2176191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2793341184_2825341184 :
    ThetaLowerSegment 2793341184 2825341184 (55865469650827 / 20000)
      (282528446994899 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2793341184 cell2793472256)
                  (ThetaLowerSegment.join cell2793603328 cell2793734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2793865472 cell2793996544)
                  (ThetaLowerSegment.join cell2794127616 cell2794258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2794389760 cell2794520832)
                  (ThetaLowerSegment.join cell2794651904 cell2794782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2794914048 cell2795045120)
                  (ThetaLowerSegment.join cell2795176192 cell2795307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2795438336 cell2795569408)
                  (ThetaLowerSegment.join cell2795700480 cell2795831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2795962624 cell2796093696)
                  (ThetaLowerSegment.join cell2796224768 cell2796355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2796486912 cell2796617984)
                  (ThetaLowerSegment.join cell2796749056 cell2796880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2797011200 cell2797142272)
                  (ThetaLowerSegment.join cell2797273344 cell2797404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2797535488 cell2797666560)
                  (ThetaLowerSegment.join cell2797797632 cell2797928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2798059776 cell2798190848)
                  (ThetaLowerSegment.join cell2798321920 cell2798452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2798584064 cell2798715136)
                  (ThetaLowerSegment.join cell2798846208 cell2798977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2799108352 cell2799239424)
                  (ThetaLowerSegment.join cell2799370496 cell2799501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2799632640 cell2799763712)
                  (ThetaLowerSegment.join cell2799894784 cell2800025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2800156928 cell2800288000)
                  (ThetaLowerSegment.join cell2800419072 cell2800550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2800681216 cell2800812288)
                  (ThetaLowerSegment.join cell2800943360 cell2801074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2801205504 cell2801336576)
                  (ThetaLowerSegment.join cell2801467648 cell2801598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2801729792 cell2801860864)
                  (ThetaLowerSegment.join cell2801991936 cell2802123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2802254080 cell2802385152)
                  (ThetaLowerSegment.join cell2802516224 cell2802647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2802778368 cell2802909440)
                  (ThetaLowerSegment.join cell2803040512 cell2803171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2803302656 cell2803433728)
                  (ThetaLowerSegment.join cell2803564800 cell2803695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2803826944 cell2803958016)
                  (ThetaLowerSegment.join cell2804089088 cell2804220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2804351232 cell2804482304)
                  (ThetaLowerSegment.join cell2804613376 cell2804744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2804875520 cell2805006592)
                  (ThetaLowerSegment.join cell2805137664 cell2805268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2805399808 cell2805530880)
                  (ThetaLowerSegment.join cell2805661952 cell2805793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2805924096 cell2806055168)
                  (ThetaLowerSegment.join cell2806186240 cell2806317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2806448384 cell2806579456)
                  (ThetaLowerSegment.join cell2806710528 cell2806841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2806972672 cell2807103744)
                  (ThetaLowerSegment.join cell2807234816 cell2807365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2807496960 cell2807628032)
                  (ThetaLowerSegment.join cell2807759104 cell2807890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2808021248 cell2808152320)
                  (ThetaLowerSegment.join cell2808283392 cell2808414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2808545536 cell2808676608)
                  (ThetaLowerSegment.join cell2808807680 cell2808938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2809069824 cell2809200896)
                  (ThetaLowerSegment.join cell2809331968 cell2809463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2809594112 cell2809725184)
                  (ThetaLowerSegment.join cell2809856256 cell2809987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2810118400 cell2810249472)
                  (ThetaLowerSegment.join cell2810380544 cell2810511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2810642688 cell2810773760)
                  (ThetaLowerSegment.join cell2810904832 cell2811035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2811166976 cell2811298048)
                  (ThetaLowerSegment.join cell2811429120 cell2811560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2811691264 cell2811822336)
                  (ThetaLowerSegment.join cell2811953408 cell2812084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2812215552 cell2812346624)
                  (ThetaLowerSegment.join cell2812477696 cell2812608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2812739840 cell2812870912)
                  (ThetaLowerSegment.join cell2813001984 cell2813133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2813264128 cell2813395200)
                  (ThetaLowerSegment.join cell2813526272 cell2813657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2813788416 cell2813919488)
                  (ThetaLowerSegment.join cell2814050560 cell2814181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2814312704 cell2814443776)
                  (ThetaLowerSegment.join cell2814574848 cell2814705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2814836992 cell2814968064)
                  (ThetaLowerSegment.join cell2815099136 cell2815230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2815361280 cell2815492352)
                  (ThetaLowerSegment.join cell2815623424 cell2815754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2815885568 cell2816016640)
                  (ThetaLowerSegment.join cell2816147712 cell2816278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2816409856 cell2816540928)
                  (ThetaLowerSegment.join cell2816672000 cell2816803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2816934144 cell2817065216)
                  (ThetaLowerSegment.join cell2817196288 cell2817327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2817458432 cell2817589504)
                  (ThetaLowerSegment.join cell2817720576 cell2817851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2817982720 cell2818113792)
                  (ThetaLowerSegment.join cell2818244864 cell2818375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2818507008 cell2818638080)
                  (ThetaLowerSegment.join cell2818769152 cell2818900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2819031296 cell2819162368)
                  (ThetaLowerSegment.join cell2819293440 cell2819424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2819555584 cell2819686656)
                  (ThetaLowerSegment.join cell2819817728 cell2819948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2820079872 cell2820210944)
                  (ThetaLowerSegment.join cell2820342016 cell2820473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2820604160 cell2820735232)
                  (ThetaLowerSegment.join cell2820866304 cell2820997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2821128448 cell2821259520)
                  (ThetaLowerSegment.join cell2821390592 cell2821521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2821652736 cell2821783808)
                  (ThetaLowerSegment.join cell2821914880 cell2822045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2822177024 cell2822308096)
                  (ThetaLowerSegment.join cell2822439168 cell2822570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2822701312 cell2822832384)
                  (ThetaLowerSegment.join cell2822963456 cell2823094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2823225600 cell2823356672)
                  (ThetaLowerSegment.join cell2823487744 cell2823618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2823749888 cell2823880960)
                  (ThetaLowerSegment.join cell2824012032 cell2824143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2824274176 cell2824405248)
                  (ThetaLowerSegment.join cell2824536320 cell2824667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2824798464 cell2824929536)
                (ThetaLowerSegment.join cell2825060608 cell2825191680))
              (ThetaLowerSegment.join cell2825322752 cell2825339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
