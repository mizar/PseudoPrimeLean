/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1993341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1961341184 :
    ThetaLowerSegment 1961341184 1961472256 (196127600570263 / 100000)
      (196140663365503 / 100000) := by
  exact
    packedTile65536 1961341184 1961472256 14 6105 44287 31 _ _ (267461 / 12500) (2139691 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961472256 :
    ThetaLowerSegment 1961472256 1961603328 (196140663365503 / 100000)
      (196153861004263 / 100000) := by
  exact
    packedTile65536 1961472256 1961603328 14 6168 44288 31 _ _ (427939 / 20000) (1069849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961603328 :
    ThetaLowerSegment 1961603328 1961734400 (196153861004263 / 100000)
      (196167028724217 / 100000) := by
  exact
    packedTile65536 1961603328 1961734400 14 6154 44289 31 _ _ (2139701 / 100000) (267463 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961734400 :
    ThetaLowerSegment 1961734400 1961865472 (196167028724217 / 100000)
      (196180102340097 / 100000) := by
  exact
    packedTile65536 1961734400 1961865472 14 6110 44291 31 _ _ (534927 / 25000) (2139711 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961865472 :
    ThetaLowerSegment 1961865472 1961996544 (196180102340097 / 100000)
      (196193321499367 / 100000) := by
  exact
    packedTile65536 1961865472 1961996544 14 6178 44292 31 _ _ (427943 / 20000) (1069859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1961996544 :
    ThetaLowerSegment 1961996544 1962127616 (196193321499367 / 100000)
      (98103198667199 / 50000) := by
  exact
    packedTile65536 1961996544 1962127616 14 6111 44294 31 _ _ (2139721 / 100000) (534931 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1962127616 :
    ThetaLowerSegment 1962127616 1962258688 (98103198667199 / 50000) (98109763352703 / 50000) := by
  exact
    packedTile65536 1962127616 1962258688 14 6136 44295 31 _ _ (133733 / 6250) (2139731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1962258688 :
    ThetaLowerSegment 1962258688 1962389760 (98109763352703 / 50000)
      (196232701053801 / 100000) := by
  exact
    packedTile65536 1962258688 1962389760 14 6157 44297 31 _ _ (427947 / 20000) (1069869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1962389760 :
    ThetaLowerSegment 1962389760 1962520832 (196232701053801 / 100000) (12265346619939 / 6250) := by
  exact
    packedTile65536 1962389760 1962520832 14 6003 44298 31 _ _ (2139741 / 100000) (66867 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1962520832 :
    ThetaLowerSegment 1962520832 1962651904 (12265346619939 / 6250) (24532308214681 / 12500) := by
  exact
    packedTile65536 1962520832 1962651904 14 6038 44300 31 _ _ (534937 / 25000) (2139751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1962651904 :
    ThetaLowerSegment 1962651904 1962782976 (24532308214681 / 12500) (98135825443879 / 50000) := by
  exact
    packedTile65536 1962651904 1962782976 14 6162 44301 31 _ _ (427951 / 20000) (1069879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1962782976 :
    ThetaLowerSegment 1962782976 1962914048 (98135825443879 / 50000) (981423752523 / 500) := by
  exact
    packedTile65536 1962782976 1962914048 14 6122 44303 31 _ _ (2139761 / 100000) (534941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1962914048 :
    ThetaLowerSegment 1962914048 1963045120 (981423752523 / 500) (24537224316291 / 12500) := by
  exact
    packedTile65536 1962914048 1963045120 14 6096 44304 31 _ _ (267471 / 12500) (2139771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963045120 :
    ThetaLowerSegment 1963045120 1963176192 (24537224316291 / 12500)
      (196310943447703 / 100000) := by
  exact
    packedTile65536 1963045120 1963176192 14 6145 44306 31 _ _ (85591 / 4000) (1069889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963176192 :
    ThetaLowerSegment 1963176192 1963307264 (196310943447703 / 100000) (4908102951983 / 2500) := by
  exact
    packedTile65536 1963176192 1963307264 14 6157 44307 31 _ _ (2139781 / 100000) (267473 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963307264 :
    ThetaLowerSegment 1963307264 1963438336 (4908102951983 / 2500) (49084302860523 / 25000) := by
  exact
    packedTile65536 1963307264 1963438336 14 6119 44309 31 _ _ (534947 / 25000) (2139791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963438336 :
    ThetaLowerSegment 1963438336 1963569408 (49084302860523 / 25000)
      (196350334804827 / 100000) := by
  exact
    packedTile65536 1963438336 1963569408 14 6133 44310 31 _ _ (427959 / 20000) (1069899 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963569408 :
    ThetaLowerSegment 1963569408 1963700480 (196350334804827 / 100000)
      (39272715178683 / 20000) := by
  exact
    packedTile65536 1963569408 1963700480 14 6188 44312 31 _ _ (2139801 / 100000) (534951 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963700480 :
    ThetaLowerSegment 1963700480 1963831552 (39272715178683 / 20000)
      (196376645840679 / 100000) := by
  exact
    packedTile65536 1963700480 1963831552 14 6108 44313 31 _ _ (66869 / 3125) (2139811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963831552 :
    ThetaLowerSegment 1963831552 1963962624 (196376645840679 / 100000)
      (196389869897379 / 100000) := by
  exact
    packedTile65536 1963831552 1963962624 14 6180 44315 31 _ _ (427963 / 20000) (1069909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1963962624 :
    ThetaLowerSegment 1963962624 1964093696 (196389869897379 / 100000)
      (196402828659411 / 100000) := by
  exact
    packedTile65536 1963962624 1964093696 14 6056 44316 31 _ _ (1069911 / 50000) (85593 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964093696 :
    ThetaLowerSegment 1964093696 1964224768 (196402828659411 / 100000)
      (196415772478983 / 100000) := by
  exact
    packedTile65536 1964093696 1964224768 14 6049 44318 31 _ _ (534957 / 25000) (2139831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964224768 :
    ThetaLowerSegment 1964224768 1964355840 (196415772478983 / 100000)
      (196429013777963 / 100000) := by
  exact
    packedTile65536 1964224768 1964355840 14 6188 44319 31 _ _ (427967 / 20000) (1069919 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964355840 :
    ThetaLowerSegment 1964355840 1964486912 (196429013777963 / 100000)
      (39288411650959 / 20000) := by
  exact
    packedTile65536 1964355840 1964486912 14 6096 44321 31 _ _ (1069921 / 50000) (427969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964486912 :
    ThetaLowerSegment 1964486912 1964617984 (39288411650959 / 20000)
      (196455151984707 / 100000) := by
  exact
    packedTile65536 1964486912 1964617984 14 6119 44322 31 _ _ (267481 / 12500) (2139851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964617984 :
    ThetaLowerSegment 1964617984 1964749056 (196455151984707 / 100000)
      (49117069998783 / 25000) := by
  exact
    packedTile65536 1964617984 1964749056 14 6135 44324 31 _ _ (427971 / 20000) (1069929 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964749056 :
    ThetaLowerSegment 1964749056 1964880128 (49117069998783 / 25000) (98240661227011 / 50000) := by
  exact
    packedTile65536 1964749056 1964880128 14 6095 44325 31 _ _ (1069931 / 50000) (427973 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1964880128 :
    ThetaLowerSegment 1964880128 1965011200 (98240661227011 / 50000) (19649455967747 / 10000) := by
  exact
    packedTile65536 1964880128 1965011200 14 6186 44326 31 _ _ (534967 / 25000) (2139871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965011200 :
    ThetaLowerSegment 1965011200 1965142272 (19649455967747 / 10000) (19650768995047 / 10000) := by
  exact
    packedTile65536 1965011200 1965142272 14 6136 44328 31 _ _ (17119 / 800) (1069939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965142272 :
    ThetaLowerSegment 1965142272 1965273344 (19650768995047 / 10000) (49130178853051 / 25000) := by
  exact
    packedTile65536 1965142272 1965273344 14 6087 44329 31 _ _ (1069941 / 50000) (427977 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965273344 :
    ThetaLowerSegment 1965273344 1965404416 (49130178853051 / 25000) (49133418643483 / 25000) := by
  exact
    packedTile65536 1965273344 1965404416 14 6056 44331 31 _ _ (133743 / 6250) (2139891 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965404416 :
    ThetaLowerSegment 1965404416 1965535488 (49133418643483 / 25000) (49136735480733 / 25000) := by
  exact
    packedTile65536 1965404416 1965535488 14 6200 44332 31 _ _ (427979 / 20000) (1069949 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965535488 :
    ThetaLowerSegment 1965535488 1965666560 (49136735480733 / 25000) (49140005250989 / 25000) := by
  exact
    packedTile65536 1965535488 1965666560 14 6112 44334 31 _ _ (1069951 / 50000) (427981 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965666560 :
    ThetaLowerSegment 1965666560 1965797632 (49140005250989 / 25000) (24571645272373 / 12500) := by
  exact
    packedTile65536 1965666560 1965797632 14 6141 44335 31 _ _ (534977 / 25000) (2139911 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965797632 :
    ThetaLowerSegment 1965797632 1965928704 (24571645272373 / 12500)
      (196586204960909 / 100000) := by
  exact
    packedTile65536 1965797632 1965928704 14 6095 44337 31 _ _ (427983 / 20000) (1069959 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1965928704 :
    ThetaLowerSegment 1965928704 1966059776 (196586204960909 / 100000)
      (196599326962613 / 100000) := by
  exact
    packedTile65536 1965928704 1966059776 14 6132 44338 31 _ _ (1069961 / 50000) (85597 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966059776 :
    ThetaLowerSegment 1966059776 1966190848 (196599326962613 / 100000)
      (196612650154341 / 100000) := by
  exact
    packedTile65536 1966059776 1966190848 14 6226 44340 31 _ _ (267491 / 12500) (2139931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966190848 :
    ThetaLowerSegment 1966190848 1966321920 (196612650154341 / 100000)
      (196625686638361 / 100000) := by
  exact
    packedTile65536 1966190848 1966321920 14 6092 44341 31 _ _ (427987 / 20000) (1069969 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966321920 :
    ThetaLowerSegment 1966321920 1966452992 (196625686638361 / 100000)
      (196638624727693 / 100000) := by
  exact
    packedTile65536 1966321920 1966452992 14 6046 44343 31 _ _ (1069971 / 50000) (427989 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966452992 :
    ThetaLowerSegment 1966452992 1966584064 (196638624727693 / 100000)
      (196651738329037 / 100000) := by
  exact
    packedTile65536 1966452992 1966584064 14 6128 44344 31 _ _ (534987 / 25000) (2139951 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966584064 :
    ThetaLowerSegment 1966584064 1966715136 (196651738329037 / 100000)
      (49166224228083 / 25000) := by
  exact
    packedTile65536 1966584064 1966715136 14 6149 44346 31 _ _ (427991 / 20000) (1069979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966715136 :
    ThetaLowerSegment 1966715136 1966846208 (49166224228083 / 25000) (24584733670247 / 12500) := by
  exact
    packedTile65536 1966715136 1966846208 14 6062 44347 31 _ _ (1069981 / 50000) (427993 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966846208 :
    ThetaLowerSegment 1966846208 1966977280 (24584733670247 / 12500) (24586365128351 / 12500) := by
  exact
    packedTile65536 1966846208 1966977280 14 6099 44349 31 _ _ (66874 / 3125) (2139971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1966977280 :
    ThetaLowerSegment 1966977280 1967108352 (24586365128351 / 12500) (98351993857079 / 50000) := by
  exact
    packedTile65536 1966977280 1967108352 14 6106 44350 31 _ _ (85599 / 4000) (1069989 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1967108352 :
    ThetaLowerSegment 1967108352 1967239424 (98351993857079 / 50000) (98358458742701 / 50000) := by
  exact
    packedTile65536 1967108352 1967239424 14 6042 44352 31 _ _ (1069991 / 50000) (427997 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1967239424 :
    ThetaLowerSegment 1967239424 1967370496 (98358458742701 / 50000) (98365075585597 / 50000) := by
  exact
    packedTile65536 1967239424 1967370496 14 6184 44353 31 _ _ (534997 / 25000) (2139991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1967370496 :
    ThetaLowerSegment 1967370496 1967501568 (98365075585597 / 50000)
      (196743066041019 / 100000) := by
  exact
    packedTile65536 1967370496 1967501568 14 6035 44355 31 _ _ (427999 / 20000) (1069999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1967501568 :
    ThetaLowerSegment 1967501568 1967632640 (196743066041019 / 100000)
      (196756207793301 / 100000) := by
  exact
    packedTile65536 1967501568 1967632640 14 6141 44356 31 _ _ (1070001 / 50000) (428001 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1967632640 :
    ThetaLowerSegment 1967632640 1967763712 (196756207793301 / 100000)
      (39353845092393 / 20000) := by
  exact
    packedTile65536 1967632640 1967763712 14 6083 44358 31 _ _ (267501 / 12500) (2140011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1967763712 :
    ThetaLowerSegment 1967763712 1967894784 (39353845092393 / 20000) (39356493574957 / 20000) := by
  exact
    packedTile65536 1967763712 1967894784 14 6188 44359 31 _ _ (428003 / 20000) (1070009 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1967894784 :
    ThetaLowerSegment 1967894784 1968025856 (39356493574957 / 20000)
      (196795616169953 / 100000) := by
  exact
    packedTile65536 1967894784 1968025856 14 6144 44360 31 _ _ (1070011 / 50000) (85601 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968025856 :
    ThetaLowerSegment 1968025856 1968156928 (196795616169953 / 100000)
      (196808702441173 / 100000) := by
  exact
    packedTile65536 1968025856 1968156928 14 6115 44362 31 _ _ (535007 / 25000) (2140031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968156928 :
    ThetaLowerSegment 1968156928 1968288000 (196808702441173 / 100000)
      (196821808015513 / 100000) := by
  exact
    packedTile65536 1968156928 1968288000 14 6124 44363 31 _ _ (428007 / 20000) (1070019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968288000 :
    ThetaLowerSegment 1968288000 1968419072 (196821808015513 / 100000)
      (196835093390041 / 100000) := by
  exact
    packedTile65536 1968288000 1968419072 14 6208 44365 31 _ _ (2140041 / 100000) (535011 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968419072 :
    ThetaLowerSegment 1968419072 1968550144 (196835093390041 / 100000)
      (196848211884281 / 100000) := by
  exact
    packedTile65536 1968419072 1968550144 14 6130 44366 31 _ _ (133753 / 6250) (2140051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968550144 :
    ThetaLowerSegment 1968550144 1968681216 (196848211884281 / 100000)
      (98430666280743 / 50000) := by
  exact
    packedTile65536 1968550144 1968681216 14 6131 44368 31 _ _ (428011 / 20000) (1070029 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968681216 :
    ThetaLowerSegment 1968681216 1968812288 (98430666280743 / 50000)
      (196874521757429 / 100000) := by
  exact
    packedTile65536 1968681216 1968812288 14 6163 44369 31 _ _ (2140061 / 100000) (66877 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968812288 :
    ThetaLowerSegment 1968812288 1968943360 (196874521757429 / 100000)
      (196887567611957 / 100000) := by
  exact
    packedTile65536 1968812288 1968943360 14 6096 44371 31 _ _ (535017 / 25000) (2140071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1968943360 :
    ThetaLowerSegment 1968943360 1969074432 (196887567611957 / 100000)
      (196900767594557 / 100000) := by
  exact
    packedTile65536 1968943360 1969074432 14 6168 44372 31 _ _ (85603 / 4000) (1070039 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969074432 :
    ThetaLowerSegment 1969074432 1969205504 (196900767594557 / 100000)
      (196913787847361 / 100000) := by
  exact
    packedTile65536 1969074432 1969205504 14 6084 44374 31 _ _ (2140081 / 100000) (535021 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969205504 :
    ThetaLowerSegment 1969205504 1969336576 (196913787847361 / 100000)
      (196926831683721 / 100000) := by
  exact
    packedTile65536 1969205504 1969336576 14 6095 44375 31 _ _ (267511 / 12500) (2140091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969336576 :
    ThetaLowerSegment 1969336576 1969467648 (196926831683721 / 100000)
      (49234997781969 / 25000) := by
  exact
    packedTile65536 1969336576 1969467648 14 6149 44377 31 _ _ (428019 / 20000) (1070049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969467648 :
    ThetaLowerSegment 1969467648 1969598720 (49234997781969 / 25000) (98476542132897 / 50000) := by
  exact
    packedTile65536 1969467648 1969598720 14 6118 44378 31 _ _ (2140101 / 100000) (267513 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969598720 :
    ThetaLowerSegment 1969598720 1969729792 (98476542132897 / 50000) (98483102633971 / 50000) := by
  exact
    packedTile65536 1969598720 1969729792 14 6131 44380 31 _ _ (535027 / 25000) (2140111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969729792 :
    ThetaLowerSegment 1969729792 1969860864 (98483102633971 / 50000) (98489736990471 / 50000) := by
  exact
    packedTile65536 1969729792 1969860864 14 6200 44381 31 _ _ (428023 / 20000) (1070059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969860864 :
    ThetaLowerSegment 1969860864 1969991936 (98489736990471 / 50000)
      (196992603623277 / 100000) := by
  exact
    packedTile65536 1969860864 1969991936 14 6135 44383 31 _ _ (2140121 / 100000) (535031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1969991936 :
    ThetaLowerSegment 1969991936 1970123008 (196992603623277 / 100000)
      (197005598480493 / 100000) := by
  exact
    packedTile65536 1969991936 1970123008 14 6072 44384 31 _ _ (66879 / 3125) (2140131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1970123008 :
    ThetaLowerSegment 1970123008 1970254080 (197005598480493 / 100000)
      (98509287059499 / 50000) := by
  exact
    packedTile65536 1970123008 1970254080 14 6063 44386 31 _ _ (428027 / 20000) (1070069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1970254080 :
    ThetaLowerSegment 1970254080 1970385152 (98509287059499 / 50000) (98515810209267 / 50000) := by
  exact
    packedTile65536 1970254080 1970385152 14 6096 44387 31 _ _ (2140141 / 100000) (133759 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1970385152 :
    ThetaLowerSegment 1970385152 1970516224 (98515810209267 / 50000) (98522277736523 / 50000) := by
  exact
    packedTile65536 1970385152 1970516224 14 6044 44389 31 _ _ (535037 / 25000) (2140151 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1970516224 :
    ThetaLowerSegment 1970516224 1970647296 (98522277736523 / 50000) (98528770966793 / 50000) := by
  exact
    packedTile65536 1970516224 1970647296 14 6068 44390 31 _ _ (428031 / 20000) (1070079 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1970647296 :
    ThetaLowerSegment 1970647296 1970778368 (98528770966793 / 50000) (98535285616877 / 50000) := by
  exact
    packedTile65536 1970647296 1970778368 14 6088 44391 31 _ _ (2140161 / 100000) (535041 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1970778368 :
    ThetaLowerSegment 1970778368 1970909440 (98535285616877 / 50000) (98541896595829 / 50000) := by
  exact
    packedTile65536 1970778368 1970909440 14 6178 44393 31 _ _ (267521 / 12500) (2140171 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1970909440 :
    ThetaLowerSegment 1970909440 1971040512 (98541896595829 / 50000)
      (197097137182783 / 100000) := by
  exact
    packedTile65536 1970909440 1971040512 14 6235 44394 31 _ _ (85607 / 4000) (1070089 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971040512 :
    ThetaLowerSegment 1971040512 1971171584 (197097137182783 / 100000)
      (197110205127969 / 100000) := by
  exact
    packedTile65536 1971040512 1971171584 14 6106 44396 31 _ _ (2140181 / 100000) (267523 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971171584 :
    ThetaLowerSegment 1971171584 1971302656 (197110205127969 / 100000)
      (197123315919657 / 100000) := by
  exact
    packedTile65536 1971171584 1971302656 14 6126 44397 31 _ _ (535047 / 25000) (2140191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971302656 :
    ThetaLowerSegment 1971302656 1971433728 (197123315919657 / 100000)
      (24642080899289 / 12500) := by
  exact
    packedTile65536 1971302656 1971433728 14 6229 44399 31 _ _ (428039 / 20000) (1070099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971433728 :
    ThetaLowerSegment 1971433728 1971564800 (24642080899289 / 12500) (98574896154427 / 50000) := by
  exact
    packedTile65536 1971433728 1971564800 14 6142 44400 31 _ _ (2140201 / 100000) (535051 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971564800 :
    ThetaLowerSegment 1971564800 1971695872 (98574896154427 / 50000) (19716310868303 / 10000) := by
  exact
    packedTile65536 1971564800 1971695872 14 6222 44402 31 _ _ (133763 / 6250) (2140211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971695872 :
    ThetaLowerSegment 1971695872 1971826944 (19716310868303 / 10000) (98588077713787 / 50000) := by
  exact
    packedTile65536 1971695872 1971826944 14 6096 44403 31 _ _ (1070107 / 50000) (2140217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971826944 :
    ThetaLowerSegment 1971826944 1971958016 (98588077713787 / 50000)
      (197189208635453 / 100000) := by
  exact
    packedTile65536 1971826944 1971958016 14 6099 44405 31 _ _ (2140221 / 100000) (66882 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1971958016 :
    ThetaLowerSegment 1971958016 1972089088 (197189208635453 / 100000)
      (197202373177881 / 100000) := by
  exact
    packedTile65536 1971958016 1972089088 14 6151 44406 31 _ _ (535057 / 25000) (2140231 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972089088 :
    ThetaLowerSegment 1972089088 1972220160 (197202373177881 / 100000)
      (197215554879087 / 100000) := by
  exact
    packedTile65536 1972089088 1972220160 14 6159 44408 31 _ _ (1070117 / 50000) (2140237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972220160 :
    ThetaLowerSegment 1972220160 1972351232 (197215554879087 / 100000)
      (197228618910151 / 100000) := by
  exact
    packedTile65536 1972220160 1972351232 14 6104 44409 31 _ _ (2140241 / 100000) (535061 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972351232 :
    ThetaLowerSegment 1972351232 1972482304 (197228618910151 / 100000)
      (197241668002207 / 100000) := by
  exact
    packedTile65536 1972351232 1972482304 14 6097 44411 31 _ _ (267531 / 12500) (2140251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972482304 :
    ThetaLowerSegment 1972482304 1972613376 (197241668002207 / 100000)
      (197255121638851 / 100000) := by
  exact
    packedTile65536 1972482304 1972613376 14 6286 44412 31 _ _ (1070127 / 50000) (2140257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972613376 :
    ThetaLowerSegment 1972613376 1972744448 (197255121638851 / 100000)
      (197268177230951 / 100000) := by
  exact
    packedTile65536 1972613376 1972744448 14 6100 44414 31 _ _ (2140261 / 100000) (267533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972744448 :
    ThetaLowerSegment 1972744448 1972875520 (197268177230951 / 100000)
      (197281376263707 / 100000) := by
  exact
    packedTile65536 1972744448 1972875520 14 6167 44415 31 _ _ (535067 / 25000) (2140271 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1972875520 :
    ThetaLowerSegment 1972875520 1973006592 (197281376263707 / 100000)
      (197294344183873 / 100000) := by
  exact
    packedTile65536 1972875520 1973006592 14 6059 44417 31 _ _ (1070137 / 50000) (2140277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973006592 :
    ThetaLowerSegment 1973006592 1973137664 (197294344183873 / 100000)
      (98653722421937 / 50000) := by
  exact
    packedTile65536 1973006592 1973137664 14 6121 44418 31 _ _ (2140281 / 100000) (535071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973137664 :
    ThetaLowerSegment 1973137664 1973268736 (98653722421937 / 50000) (98660286685233 / 50000) := by
  exact
    packedTile65536 1973137664 1973268736 14 6134 44420 31 _ _ (66884 / 3125) (2140291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973268736 :
    ThetaLowerSegment 1973268736 1973399808 (98660286685233 / 50000) (24666696421991 / 12500) := by
  exact
    packedTile65536 1973268736 1973399808 14 6073 44421 31 _ _ (1070147 / 50000) (2140297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973399808 :
    ThetaLowerSegment 1973399808 1973530880 (24666696421991 / 12500) (98673255817887 / 50000) := by
  exact
    packedTile65536 1973399808 1973530880 14 6046 44422 31 _ _ (2140301 / 100000) (133769 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973530880 :
    ThetaLowerSegment 1973530880 1973661952 (98673255817887 / 50000) (98679825493293 / 50000) := by
  exact
    packedTile65536 1973530880 1973661952 14 6139 44424 31 _ _ (535077 / 25000) (2140311 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973661952 :
    ThetaLowerSegment 1973661952 1973793024 (98679825493293 / 50000) (3947455251003 / 2000) := by
  exact
    packedTile65536 1973661952 1973793024 14 6126 44425 31 _ _ (1070157 / 50000) (2140317 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973793024 :
    ThetaLowerSegment 1973793024 1973924096 (3947455251003 / 2000) (12336620880349 / 6250) := by
  exact
    packedTile65536 1973793024 1973924096 14 6154 44427 31 _ _ (2140321 / 100000) (535081 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1973924096 :
    ThetaLowerSegment 1973924096 1974055168 (12336620880349 / 6250) (98699582793549 / 50000) := by
  exact
    packedTile65536 1973924096 1974055168 14 6182 44428 31 _ _ (2140327 / 100000) (214033 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974055168 :
    ThetaLowerSegment 1974055168 1974186240 (98699582793549 / 50000) (49353076274381 / 25000) := by
  exact
    packedTile65536 1974055168 1974186240 14 6139 44430 31 _ _ (1070167 / 50000) (2140337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974186240 :
    ThetaLowerSegment 1974186240 1974317312 (49353076274381 / 25000) (98712738378019 / 50000) := by
  exact
    packedTile65536 1974186240 1974317312 14 6154 44431 31 _ _ (2140341 / 100000) (267543 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974317312 :
    ThetaLowerSegment 1974317312 1974448384 (98712738378019 / 50000)
      (197438539293779 / 100000) := by
  exact
    packedTile65536 1974317312 1974448384 14 6103 44433 31 _ _ (2140347 / 100000) (42807 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974448384 :
    ThetaLowerSegment 1974448384 1974579456 (197438539293779 / 100000)
      (197451803067517 / 100000) := by
  exact
    packedTile65536 1974448384 1974579456 14 6197 44434 31 _ _ (1070177 / 50000) (2140357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974579456 :
    ThetaLowerSegment 1974579456 1974710528 (197451803067517 / 100000)
      (197465000533443 / 100000) := by
  exact
    packedTile65536 1974579456 1974710528 14 6166 44436 31 _ _ (2140361 / 100000) (535091 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974710528 :
    ThetaLowerSegment 1974710528 1974841600 (197465000533443 / 100000)
      (197477902665719 / 100000) := by
  exact
    packedTile65536 1974710528 1974841600 14 6028 44437 31 _ _ (2140367 / 100000) (214037 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974841600 :
    ThetaLowerSegment 1974841600 1974972672 (197477902665719 / 100000)
      (39498227747707 / 20000) := by
  exact
    packedTile65536 1974841600 1974972672 14 6184 44439 31 _ _ (1070187 / 50000) (2140377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1974972672 :
    ThetaLowerSegment 1974972672 1975103744 (39498227747707 / 20000)
      (197504284958637 / 100000) := by
  exact
    packedTile65536 1974972672 1975103744 14 6142 44440 31 _ _ (2140381 / 100000) (66887 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1975103744 :
    ThetaLowerSegment 1975103744 1975234816 (197504284958637 / 100000) (3950346783579 / 2000) := by
  exact
    packedTile65536 1975103744 1975234816 14 6099 44442 31 _ _ (2140387 / 100000) (214039 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1975234816 :
    ThetaLowerSegment 1975234816 1975365888 (3950346783579 / 2000) (98765242739449 / 50000) := by
  exact
    packedTile65536 1975234816 1975365888 14 6142 44443 31 _ _ (1070197 / 50000) (2140397 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1975365888 :
    ThetaLowerSegment 1975365888 1975496960 (98765242739449 / 50000) (98771842662849 / 50000) := by
  exact
    packedTile65536 1975365888 1975496960 14 6167 44445 31 _ _ (5351 / 250) (2140403 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1975496960 :
    ThetaLowerSegment 1975496960 1975628032 (98771842662849 / 50000)
      (197556756791247 / 100000) := by
  exact
    packedTile65536 1975496960 1975628032 14 6107 44446 31 _ _ (2140407 / 100000) (214041 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1975628032 :
    ThetaLowerSegment 1975628032 1975759104 (197556756791247 / 100000)
      (197569736261743 / 100000) := by
  exact
    packedTile65536 1975628032 1975759104 14 6064 44448 31 _ _ (1070207 / 50000) (2140417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1975759104 :
    ThetaLowerSegment 1975759104 1975890176 (197569736261743 / 100000)
      (197582833491723 / 100000) := by
  exact
    packedTile65536 1975759104 1975890176 14 6119 44449 31 _ _ (107021 / 5000) (2140423 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1975890176 :
    ThetaLowerSegment 1975890176 1976021248 (197582833491723 / 100000)
      (197595830164467 / 100000) := by
  exact
    packedTile65536 1975890176 1976021248 14 6072 44450 31 _ _ (2140427 / 100000) (214043 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976021248 :
    ThetaLowerSegment 1976021248 1976152320 (197595830164467 / 100000)
      (197608886811867 / 100000) := by
  exact
    packedTile65536 1976021248 1976152320 14 6100 44452 31 _ _ (1070217 / 50000) (2140437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976152320 :
    ThetaLowerSegment 1976152320 1976283392 (197608886811867 / 100000)
      (197621999147307 / 100000) := by
  exact
    packedTile65536 1976152320 1976283392 14 6126 44453 31 _ _ (53511 / 2500) (2140443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976283392 :
    ThetaLowerSegment 1976283392 1976414464 (197621999147307 / 100000)
      (98817631748683 / 50000) := by
  exact
    packedTile65536 1976283392 1976414464 14 6197 44455 31 _ _ (2140447 / 100000) (42809 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976414464 :
    ThetaLowerSegment 1976414464 1976545536 (98817631748683 / 50000) (98824211504279 / 50000) := by
  exact
    packedTile65536 1976414464 1976545536 14 6148 44456 31 _ _ (1070227 / 50000) (2140457 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976545536 :
    ThetaLowerSegment 1976545536 1976676608 (98824211504279 / 50000) (98830801980619 / 50000) := by
  exact
    packedTile65536 1976545536 1976676608 14 6158 44458 31 _ _ (107023 / 5000) (2140463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976676608 :
    ThetaLowerSegment 1976676608 1976807680 (98830801980619 / 50000) (9883737963571 / 5000) := by
  exact
    packedTile65536 1976676608 1976807680 14 6146 44459 31 _ _ (2140467 / 100000) (214047 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976807680 :
    ThetaLowerSegment 1976807680 1976938752 (9883737963571 / 5000) (9884380105471 / 5000) := by
  exact
    packedTile65536 1976807680 1976938752 14 6000 44461 31 _ _ (2140473 / 100000) (535119 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1976938752 :
    ThetaLowerSegment 1976938752 1977069824 (9884380105471 / 5000) (9885035627471 / 5000) := by
  exact
    packedTile65536 1976938752 1977069824 14 6125 44462 31 _ _ (13378 / 625) (2140483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977069824 :
    ThetaLowerSegment 1977069824 1977200896 (9885035627471 / 5000) (39542773168407 / 20000) := by
  exact
    packedTile65536 1977069824 1977200896 14 6145 44464 31 _ _ (2140487 / 100000) (214049 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977200896 :
    ThetaLowerSegment 1977200896 1977331968 (39542773168407 / 20000)
      (197727076964831 / 100000) := by
  exact
    packedTile65536 1977200896 1977331968 14 6172 44465 31 _ _ (2140493 / 100000) (133781 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977331968 :
    ThetaLowerSegment 1977331968 1977463040 (197727076964831 / 100000)
      (197740226056331 / 100000) := by
  exact
    packedTile65536 1977331968 1977463040 14 6143 44467 31 _ _ (4281 / 200) (2140503 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977463040 :
    ThetaLowerSegment 1977463040 1977594112 (197740226056331 / 100000)
      (197753300273087 / 100000) := by
  exact
    packedTile65536 1977463040 1977594112 14 6108 44468 31 _ _ (2140507 / 100000) (214051 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977594112 :
    ThetaLowerSegment 1977594112 1977725184 (197753300273087 / 100000)
      (197766400212647 / 100000) := by
  exact
    packedTile65536 1977594112 1977725184 14 6120 44470 31 _ _ (2140513 / 100000) (535129 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977725184 :
    ThetaLowerSegment 1977725184 1977856256 (197766400212647 / 100000)
      (197779423136327 / 100000) := by
  exact
    packedTile65536 1977725184 1977856256 14 6084 44471 31 _ _ (53513 / 2500) (2140523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977856256 :
    ThetaLowerSegment 1977856256 1977987328 (197779423136327 / 100000)
      (197792506031239 / 100000) := by
  exact
    packedTile65536 1977856256 1977987328 14 6112 44473 31 _ _ (1070263 / 50000) (2140529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1977987328 :
    ThetaLowerSegment 1977987328 1978118400 (197792506031239 / 100000)
      (98902801976333 / 50000) := by
  exact
    packedTile65536 1977987328 1978118400 14 6119 44474 31 _ _ (2140533 / 100000) (267567 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1978118400 :
    ThetaLowerSegment 1978118400 1978249472 (98902801976333 / 50000) (98909416244933 / 50000) := by
  exact
    packedTile65536 1978118400 1978249472 14 6180 44476 31 _ _ (107027 / 5000) (2140543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1978249472 :
    ThetaLowerSegment 1978249472 1978380544 (98909416244933 / 50000) (24728989170809 / 12500) := by
  exact
    packedTile65536 1978249472 1978380544 14 6111 44477 31 _ _ (1070273 / 50000) (2140549 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1978380544 :
    ThetaLowerSegment 1978380544 1978511616 (24728989170809 / 12500) (39569007419383 / 20000) := by
  exact
    packedTile65536 1978380544 1978511616 14 6131 44478 31 _ _ (2140553 / 100000) (535139 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1978511616 :
    ThetaLowerSegment 1978511616 1978642688 (39569007419383 / 20000) (39571639880071 / 20000) := by
  exact
    packedTile65536 1978511616 1978642688 14 6149 44480 31 _ _ (26757 / 1250) (2140563 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1978642688 :
    ThetaLowerSegment 1978642688 1978773760 (39571639880071 / 20000)
      (197871507299177 / 100000) := by
  exact
    packedTile65536 1978642688 1978773760 14 6217 44481 31 _ _ (1070283 / 50000) (2140569 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1978773760 :
    ThetaLowerSegment 1978773760 1978904832 (197871507299177 / 100000)
      (197884603324791 / 100000) := by
  exact
    packedTile65536 1978773760 1978904832 14 6118 44483 31 _ _ (2140573 / 100000) (66893 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1978904832 :
    ThetaLowerSegment 1978904832 1979035904 (197884603324791 / 100000)
      (197897575233531 / 100000) := by
  exact
    packedTile65536 1978904832 1979035904 14 6060 44484 31 _ _ (2140579 / 100000) (1070291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979035904 :
    ThetaLowerSegment 1979035904 1979166976 (197897575233531 / 100000)
      (197910581434067 / 100000) := by
  exact
    packedTile65536 1979035904 1979166976 14 6076 44486 31 _ _ (1070293 / 50000) (2140589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979166976 :
    ThetaLowerSegment 1979166976 1979298048 (197910581434067 / 100000)
      (98961869829619 / 50000) := by
  exact
    packedTile65536 1979166976 1979298048 14 6147 44487 31 _ _ (2140593 / 100000) (535149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979298048 :
    ThetaLowerSegment 1979298048 1979429120 (98961869829619 / 50000)
      (197936859390509 / 100000) := by
  exact
    packedTile65536 1979298048 1979429120 14 6129 44489 31 _ _ (2140599 / 100000) (1070301 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979429120 :
    ThetaLowerSegment 1979429120 1979560192 (197936859390509 / 100000)
      (197950006992561 / 100000) := by
  exact
    packedTile65536 1979429120 1979560192 14 6142 44490 31 _ _ (1070303 / 50000) (2140609 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979560192 :
    ThetaLowerSegment 1979560192 1979691264 (197950006992561 / 100000)
      (197963009075923 / 100000) := by
  exact
    packedTile65536 1979560192 1979691264 14 6074 44492 31 _ _ (2140613 / 100000) (267577 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979691264 :
    ThetaLowerSegment 1979691264 1979822336 (197963009075923 / 100000)
      (197976199570201 / 100000) := by
  exact
    packedTile65536 1979691264 1979822336 14 6162 44493 31 _ _ (2140619 / 100000) (1070311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979822336 :
    ThetaLowerSegment 1979822336 1979953408 (197976199570201 / 100000)
      (197989231701289 / 100000) := by
  exact
    packedTile65536 1979822336 1979953408 14 6088 44495 31 _ _ (1070313 / 50000) (2140629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1979953408 :
    ThetaLowerSegment 1979953408 1980084480 (197989231701289 / 100000)
      (198002383744297 / 100000) := by
  exact
    packedTile65536 1979953408 1980084480 14 6144 44496 31 _ _ (267579 / 12500) (428127 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980084480 :
    ThetaLowerSegment 1980084480 1980215552 (198002383744297 / 100000)
      (99007766844837 / 50000) := by
  exact
    packedTile65536 1980084480 1980215552 14 6143 44498 31 _ _ (2140639 / 100000) (1070321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980215552 :
    ThetaLowerSegment 1980215552 1980346624 (99007766844837 / 50000) (49507155934991 / 25000) := by
  exact
    packedTile65536 1980215552 1980346624 14 6115 44499 31 _ _ (1070323 / 50000) (2140649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980346624 :
    ThetaLowerSegment 1980346624 1980477696 (49507155934991 / 25000) (6188804627418 / 3125) := by
  exact
    packedTile65536 1980346624 1980477696 14 6131 44501 31 _ _ (535163 / 25000) (428131 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980477696 :
    ThetaLowerSegment 1980477696 1980608768 (6188804627418 / 3125) (99027507940929 / 50000) := by
  exact
    packedTile65536 1980477696 1980608768 14 6198 44502 31 _ _ (2140659 / 100000) (1070331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980608768 :
    ThetaLowerSegment 1980608768 1980739840 (99027507940929 / 50000) (99033970611583 / 50000) := by
  exact
    packedTile65536 1980608768 1980739840 14 6038 44504 31 _ _ (1070333 / 50000) (2140669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980739840 :
    ThetaLowerSegment 1980739840 1980870912 (99033970611583 / 50000) (19808117485747 / 10000) := by
  exact
    packedTile65536 1980739840 1980870912 14 6182 44505 31 _ _ (66896 / 3125) (85627 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1980870912 :
    ThetaLowerSegment 1980870912 1981001984 (19808117485747 / 10000) (6190448661211 / 3125) := by
  exact
    packedTile65536 1980870912 1981001984 14 6158 44506 31 _ _ (2140679 / 100000) (1070341 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981001984 :
    ThetaLowerSegment 1981001984 1981133056 (6190448661211 / 3125) (198107220534917 / 100000) := by
  exact
    packedTile65536 1981001984 1981133056 14 6009 44508 31 _ _ (428137 / 20000) (133793 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981133056 :
    ThetaLowerSegment 1981133056 1981264128 (198107220534917 / 100000)
      (198120321569957 / 100000) := by
  exact
    packedTile65536 1981133056 1981264128 14 6120 44509 31 _ _ (535173 / 25000) (428139 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981264128 :
    ThetaLowerSegment 1981264128 1981395200 (198120321569957 / 100000)
      (24766690942761 / 12500) := by
  exact
    packedTile65536 1981264128 1981395200 14 6169 44511 31 _ _ (2140699 / 100000) (1070351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981395200 :
    ThetaLowerSegment 1981395200 1981526272 (24766690942761 / 12500) (99073312187639 / 50000) := by
  exact
    packedTile65536 1981395200 1981526272 14 6118 44512 31 _ _ (428141 / 20000) (535177 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981526272 :
    ThetaLowerSegment 1981526272 1981657344 (99073312187639 / 50000) (99079937691279 / 50000) := by
  exact
    packedTile65536 1981526272 1981657344 14 6190 44514 31 _ _ (267589 / 12500) (428143 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981657344 :
    ThetaLowerSegment 1981657344 1981788416 (99079937691279 / 50000) (49543276790129 / 25000) := by
  exact
    packedTile65536 1981657344 1981788416 14 6181 44515 31 _ _ (1070359 / 50000) (2140721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981788416 :
    ThetaLowerSegment 1981788416 1981919488 (49543276790129 / 25000)
      (198186069250391 / 100000) := by
  exact
    packedTile65536 1981788416 1981919488 14 6055 44517 31 _ _ (85629 / 4000) (267591 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1981919488 :
    ThetaLowerSegment 1981919488 1982050560 (198186069250391 / 100000)
      (198199224048531 / 100000) := by
  exact
    packedTile65536 1981919488 1982050560 14 6145 44518 31 _ _ (535183 / 25000) (428147 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982050560 :
    ThetaLowerSegment 1982050560 1982181632 (198199224048531 / 100000)
      (198212378883541 / 100000) := by
  exact
    packedTile65536 1982050560 1982181632 14 6145 44520 31 _ _ (1070369 / 50000) (2140741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982181632 :
    ThetaLowerSegment 1982181632 1982312704 (198212378883541 / 100000)
      (99112651280553 / 50000) := by
  exact
    packedTile65536 1982181632 1982312704 14 6037 44521 31 _ _ (428149 / 20000) (535187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982312704 :
    ThetaLowerSegment 1982312704 1982443776 (99112651280553 / 50000) (19823848317117 / 10000) := by
  exact
    packedTile65536 1982312704 1982443776 14 6157 44523 31 _ _ (133797 / 6250) (428151 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982443776 :
    ThetaLowerSegment 1982443776 1982574848 (19823848317117 / 10000) (99125721660051 / 50000) := by
  exact
    packedTile65536 1982443776 1982574848 14 6054 44524 31 _ _ (1070379 / 50000) (2140761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982574848 :
    ThetaLowerSegment 1982574848 1982705920 (99125721660051 / 50000) (24783072916959 / 12500) := by
  exact
    packedTile65536 1982574848 1982705920 14 6138 44526 31 _ _ (428153 / 20000) (66899 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982705920 :
    ThetaLowerSegment 1982705920 1982836992 (24783072916959 / 12500) (99138814597073 / 50000) := by
  exact
    packedTile65536 1982705920 1982836992 14 6094 44527 31 _ _ (2140771 / 100000) (1070387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982836992 :
    ThetaLowerSegment 1982836992 1982968064 (99138814597073 / 50000) (24786332513729 / 12500) := by
  exact
    packedTile65536 1982836992 1982968064 14 6087 44529 31 _ _ (1070389 / 50000) (2140781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1982968064 :
    ThetaLowerSegment 1982968064 1983099136 (24786332513729 / 12500)
      (198303913709767 / 100000) := by
  exact
    packedTile65536 1982968064 1983099136 14 6191 44530 31 _ _ (428157 / 20000) (535197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1983099136 :
    ThetaLowerSegment 1983099136 1983230208 (198303913709767 / 100000)
      (49579225472191 / 25000) := by
  exact
    packedTile65536 1983099136 1983230208 14 6067 44532 31 _ _ (2140791 / 100000) (1070397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1983230208 :
    ThetaLowerSegment 1983230208 1983361280 (49579225472191 / 25000) (49582492329939 / 25000) := by
  exact
    packedTile65536 1983230208 1983361280 14 6104 44533 31 _ _ (1070399 / 50000) (2140801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1983361280 :
    ThetaLowerSegment 1983361280 1983492352 (49582492329939 / 25000) (49585814857747 / 25000) := by
  exact
    packedTile65536 1983361280 1983492352 14 6208 44534 31 _ _ (535201 / 25000) (2140807 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1983492352 :
    ThetaLowerSegment 1983492352 1983623424 (49585814857747 / 25000)
      (198356264857813 / 100000) := by
  exact
    packedTile65536 1983492352 1983623424 14 6075 44536 31 _ _ (2140811 / 100000) (1070407 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1983623424 :
    ThetaLowerSegment 1983623424 1983754496 (198356264857813 / 100000)
      (198369276749617 / 100000) := by
  exact
    packedTile65536 1983623424 1983754496 14 6078 44537 31 _ _ (1070409 / 50000) (2140821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1983754496 :
    ThetaLowerSegment 1983754496 1983885568 (198369276749617 / 100000)
      (198382370029201 / 100000) := by
  exact
    packedTile65536 1983754496 1983885568 14 6116 44539 31 _ _ (267603 / 12500) (2140827 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1983885568 :
    ThetaLowerSegment 1983885568 1984016640 (198382370029201 / 100000)
      (198395519013203 / 100000) := by
  exact
    packedTile65536 1983885568 1984016640 14 6142 44540 31 _ _ (2140831 / 100000) (1070417 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984016640 :
    ThetaLowerSegment 1984016640 1984147712 (198395519013203 / 100000) (2480109929293 / 1250) := by
  exact
    packedTile65536 1984016640 1984147712 14 6201 44542 31 _ _ (2140837 / 100000) (53521 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984147712 :
    ThetaLowerSegment 1984147712 1984278784 (2480109929293 / 1250) (49605516358849 / 25000) := by
  exact
    packedTile65536 1984147712 1984278784 14 6199 44543 31 _ _ (535211 / 25000) (2140847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984278784 :
    ThetaLowerSegment 1984278784 1984409856 (49605516358849 / 25000) (99217530200483 / 50000) := by
  exact
    packedTile65536 1984278784 1984409856 14 6070 44545 31 _ _ (2140851 / 100000) (1070427 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984409856 :
    ThetaLowerSegment 1984409856 1984540928 (99217530200483 / 50000) (6201507351092 / 3125) := by
  exact
    packedTile65536 1984409856 1984540928 14 6154 44546 31 _ _ (2140857 / 100000) (107043 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984540928 :
    ThetaLowerSegment 1984540928 1984672000 (6201507351092 / 3125) (6201918865294 / 3125) := by
  exact
    packedTile65536 1984540928 1984672000 14 6151 44548 31 _ _ (66902 / 3125) (2140867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984672000 :
    ThetaLowerSegment 1984672000 1984803072 (6201918865294 / 3125) (99237337471269 / 50000) := by
  exact
    packedTile65536 1984672000 1984803072 14 6199 44549 31 _ _ (214087 / 10000) (2140873 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984803072 :
    ThetaLowerSegment 1984803072 1984934144 (99237337471269 / 50000) (99243747257007 / 50000) := by
  exact
    packedTile65536 1984803072 1984934144 14 5988 44551 31 _ _ (2140877 / 100000) (26761 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1984934144 :
    ThetaLowerSegment 1984934144 1985065216 (99243747257007 / 50000) (99250295150721 / 50000) := by
  exact
    packedTile65536 1984934144 1985065216 14 6117 44552 31 _ _ (535221 / 25000) (2140887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985065216 :
    ThetaLowerSegment 1985065216 1985196288 (99250295150721 / 50000) (99256874105691 / 50000) := by
  exact
    packedTile65536 1985065216 1985196288 14 6146 44554 31 _ _ (214089 / 10000) (2140893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985196288 :
    ThetaLowerSegment 1985196288 1985327360 (99256874105691 / 50000)
      (198526814105773 / 100000) := by
  exact
    packedTile65536 1985196288 1985327360 14 6103 44555 31 _ _ (2140897 / 100000) (21409 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985327360 :
    ThetaLowerSegment 1985327360 1985458432 (198526814105773 / 100000)
      (198539886459491 / 100000) := by
  exact
    packedTile65536 1985327360 1985458432 14 6106 44557 31 _ _ (2140903 / 100000) (1070453 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985458432 :
    ThetaLowerSegment 1985458432 1985589504 (198539886459491 / 100000)
      (198552982405961 / 100000) := by
  exact
    packedTile65536 1985458432 1985589504 14 6117 44558 31 _ _ (214091 / 10000) (2140913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985589504 :
    ThetaLowerSegment 1985589504 1985720576 (198552982405961 / 100000)
      (49641499260101 / 25000) := by
  exact
    packedTile65536 1985589504 1985720576 14 6079 44559 31 _ _ (2140917 / 100000) (53523 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985720576 :
    ThetaLowerSegment 1985720576 1985851648 (49641499260101 / 25000) (19857901813409 / 10000) := by
  exact
    packedTile65536 1985720576 1985851648 14 6082 44561 31 _ _ (2140923 / 100000) (1070463 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985851648 :
    ThetaLowerSegment 1985851648 1985982720 (19857901813409 / 10000) (248240115992 / 125) := by
  exact
    packedTile65536 1985851648 1985982720 14 6107 44562 31 _ _ (214093 / 10000) (2140933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1985982720 :
    ThetaLowerSegment 1985982720 1986113792 (248240115992 / 125) (24825652894261 / 12500) := by
  exact
    packedTile65536 1985982720 1986113792 14 6133 44564 31 _ _ (267617 / 12500) (2140939 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1986113792 :
    ThetaLowerSegment 1986113792 1986244864 (24825652894261 / 12500) (19861827006073 / 10000) := by
  exact
    packedTile65536 1986113792 1986244864 14 6094 44565 31 _ _ (2140943 / 100000) (1070473 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1986244864 :
    ThetaLowerSegment 1986244864 1986375936 (19861827006073 / 10000) (19863135126523 / 10000) := by
  exact
    packedTile65536 1986244864 1986375936 14 6110 44567 31 _ _ (42819 / 2000) (2140953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1986375936 :
    ThetaLowerSegment 1986375936 1986507008 (19863135126523 / 10000) (99322246226579 / 50000) := by
  exact
    packedTile65536 1986375936 1986507008 14 6138 44568 31 _ _ (535239 / 25000) (2140959 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1986507008 :
    ThetaLowerSegment 1986507008 1986638080 (99322246226579 / 50000) (49664408421013 / 25000) := by
  exact
    packedTile65536 1986507008 1986638080 14 6138 44570 31 _ _ (2140963 / 100000) (1070483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1986638080 :
    ThetaLowerSegment 1986638080 1986769152 (49664408421013 / 25000) (24833840981307 / 12500) := by
  exact
    packedTile65536 1986638080 1986769152 14 6116 44571 31 _ _ (2140969 / 100000) (535243 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1986769152 :
    ThetaLowerSegment 1986769152 1986900224 (24833840981307 / 12500) (24835506125391 / 12500) := by
  exact
    packedTile65536 1986769152 1986900224 14 6222 44573 31 _ _ (133811 / 6250) (2140979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1986900224 :
    ThetaLowerSegment 1986900224 1987031296 (24835506125391 / 12500)
      (198697196779731 / 100000) := by
  exact
    packedTile65536 1986900224 1987031296 14 6141 44574 31 _ _ (2140983 / 100000) (1070493 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987031296 :
    ThetaLowerSegment 1987031296 1987162368 (198697196779731 / 100000)
      (198710273940543 / 100000) := by
  exact
    packedTile65536 1987031296 1987162368 14 6108 44576 31 _ _ (2140989 / 100000) (66906 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987162368 :
    ThetaLowerSegment 1987162368 1987293440 (198710273940543 / 100000)
      (39744656954647 / 20000) := by
  exact
    packedTile65536 1987162368 1987293440 14 6077 44577 31 _ _ (535249 / 25000) (2140999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987293440 :
    ThetaLowerSegment 1987293440 1987424512 (39744656954647 / 20000)
      (198736374859463 / 100000) := by
  exact
    packedTile65536 1987293440 1987424512 14 6114 44579 31 _ _ (1070501 / 50000) (428201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987424512 :
    ThetaLowerSegment 1987424512 1987555584 (198736374859463 / 100000)
      (198749362220057 / 100000) := by
  exact
    packedTile65536 1987424512 1987555584 14 6066 44580 31 _ _ (2141009 / 100000) (535253 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987555584 :
    ThetaLowerSegment 1987555584 1987686656 (198749362220057 / 100000)
      (198762475943057 / 100000) := by
  exact
    packedTile65536 1987555584 1987686656 14 6125 44582 31 _ _ (267627 / 12500) (2141019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987686656 :
    ThetaLowerSegment 1987686656 1987817728 (198762475943057 / 100000)
      (39755151768709 / 20000) := by
  exact
    packedTile65536 1987686656 1987817728 14 6204 44583 31 _ _ (1070511 / 50000) (85641 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987817728 :
    ThetaLowerSegment 1987817728 1987948800 (39755151768709 / 20000)
      (198788879069257 / 100000) := by
  exact
    packedTile65536 1987817728 1987948800 14 6128 44584 31 _ _ (2141029 / 100000) (267629 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1987948800 :
    ThetaLowerSegment 1987948800 1988079872 (198788879069257 / 100000)
      (198801939382757 / 100000) := by
  exact
    packedTile65536 1987948800 1988079872 14 6100 44586 31 _ _ (428207 / 20000) (1070519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988079872 :
    ThetaLowerSegment 1988079872 1988210944 (198801939382757 / 100000)
      (39762986673331 / 20000) := by
  exact
    packedTile65536 1988079872 1988210944 14 6069 44587 31 _ _ (1070521 / 50000) (428209 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988210944 :
    ThetaLowerSegment 1988210944 1988342016 (39762986673331 / 20000)
      (198827959508771 / 100000) := by
  exact
    packedTile65536 1988210944 1988342016 14 6084 44589 31 _ _ (2141049 / 100000) (535263 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988342016 :
    ThetaLowerSegment 1988342016 1988473088 (198827959508771 / 100000)
      (99420536735323 / 50000) := by
  exact
    packedTile65536 1988342016 1988473088 14 6125 44590 31 _ _ (428211 / 20000) (1070529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988473088 :
    ThetaLowerSegment 1988473088 1988604160 (99420536735323 / 50000) (99427118359911 / 50000) := by
  exact
    packedTile65536 1988473088 1988604160 14 6148 44592 31 _ _ (1070531 / 50000) (428213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988604160 :
    ThetaLowerSegment 1988604160 1988735232 (99427118359911 / 50000) (99433704285079 / 50000) := by
  exact
    packedTile65536 1988604160 1988735232 14 6152 44593 31 _ _ (535267 / 25000) (2141071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988735232 :
    ThetaLowerSegment 1988735232 1988866304 (99433704285079 / 50000) (99440307360379 / 50000) := by
  exact
    packedTile65536 1988735232 1988866304 14 6168 44595 31 _ _ (85643 / 4000) (1070539 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988866304 :
    ThetaLowerSegment 1988866304 1988997376 (99440307360379 / 50000) (19889373098909 / 10000) := by
  exact
    packedTile65536 1988866304 1988997376 14 6126 44596 31 _ _ (1070541 / 50000) (428217 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1988997376 :
    ThetaLowerSegment 1988997376 1989128448 (19889373098909 / 10000) (99453415082737 / 50000) := by
  exact
    packedTile65536 1988997376 1989128448 14 6118 44598 31 _ _ (66909 / 3125) (2141091 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1989128448 :
    ThetaLowerSegment 1989128448 1989259520 (99453415082737 / 50000)
      (198919931525779 / 100000) := by
  exact
    packedTile65536 1989128448 1989259520 14 6119 44599 31 _ _ (428219 / 20000) (1070549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1989259520 :
    ThetaLowerSegment 1989259520 1989390592 (198919931525779 / 100000) (6216656877381 / 3125) := by
  exact
    packedTile65536 1989259520 1989390592 14 6113 44601 31 _ _ (2141101 / 100000) (133819 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1989390592 :
    ThetaLowerSegment 1989390592 1989521664 (6216656877381 / 3125) (12434134334403 / 6250) := by
  exact
    packedTile65536 1989390592 1989521664 14 6132 44602 31 _ _ (535277 / 25000) (2141111 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1989521664 :
    ThetaLowerSegment 1989521664 1989652736 (12434134334403 / 6250) (198959199446373 / 100000) := by
  exact
    packedTile65536 1989521664 1989652736 14 6095 44604 31 _ _ (428223 / 20000) (1070559 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1989652736 :
    ThetaLowerSegment 1989652736 1989783808 (198959199446373 / 100000)
      (198972375905007 / 100000) := by
  exact
    packedTile65536 1989652736 1989783808 14 6154 44605 31 _ _ (2141121 / 100000) (535281 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1989783808 :
    ThetaLowerSegment 1989783808 1989914880 (198972375905007 / 100000)
      (39797085644259 / 20000) := by
  exact
    packedTile65536 1989783808 1989914880 14 6096 44606 31 _ _ (267641 / 12500) (2141131 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1989914880 :
    ThetaLowerSegment 1989914880 1990045952 (39797085644259 / 20000) (39799723521347 / 20000) := by
  exact
    packedTile65536 1989914880 1990045952 14 6160 44608 31 _ _ (1070567 / 50000) (2141137 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990045952 :
    ThetaLowerSegment 1990045952 1990177024 (39799723521347 / 20000) (99505825366001 / 50000) := by
  exact
    packedTile65536 1990045952 1990177024 14 6087 44609 31 _ _ (2141141 / 100000) (267643 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990177024 :
    ThetaLowerSegment 1990177024 1990308096 (99505825366001 / 50000) (49756179002749 / 25000) := by
  exact
    packedTile65536 1990177024 1990308096 14 6102 44611 31 _ _ (2141147 / 100000) (42823 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990308096 :
    ThetaLowerSegment 1990308096 1990439168 (49756179002749 / 25000) (12439860262717 / 6250) := by
  exact
    packedTile65536 1990308096 1990439168 14 6094 44612 31 _ _ (1070577 / 50000) (2141157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990439168 :
    ThetaLowerSegment 1990439168 1990570240 (12439860262717 / 6250) (199050814579767 / 100000) := by
  exact
    packedTile65536 1990439168 1990570240 14 6095 44614 31 _ _ (2141161 / 100000) (535291 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990570240 :
    ThetaLowerSegment 1990570240 1990701312 (199050814579767 / 100000)
      (39812819675967 / 20000) := by
  exact
    packedTile65536 1990570240 1990701312 14 6204 44615 31 _ _ (2141167 / 100000) (214117 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990701312 :
    ThetaLowerSegment 1990701312 1990832384 (39812819675967 / 20000)
      (199077076035449 / 100000) := by
  exact
    packedTile65536 1990701312 1990832384 14 6061 44617 31 _ _ (1070587 / 50000) (2141177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990832384 :
    ThetaLowerSegment 1990832384 1990963456 (199077076035449 / 100000)
      (199090218598289 / 100000) := by
  exact
    packedTile65536 1990832384 1990963456 14 6138 44618 31 _ _ (107059 / 5000) (2141183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1990963456 :
    ThetaLowerSegment 1990963456 1991094528 (199090218598289 / 100000) (248878974004 / 125) := by
  exact
    packedTile65536 1990963456 1991094528 14 6053 44620 31 _ _ (2141187 / 100000) (214119 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1991094528 :
    ThetaLowerSegment 1991094528 1991225600 (248878974004 / 125) (12444769848099 / 6250) := by
  exact
    packedTile65536 1991094528 1991225600 14 6136 44621 31 _ _ (1070597 / 50000) (2141197 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1991225600 :
    ThetaLowerSegment 1991225600 1991356672 (12444769848099 / 6250) (6222798376387 / 3125) := by
  exact
    packedTile65536 1991225600 1991356672 14 6179 44623 31 _ _ (5353 / 250) (2141203 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1991356672 :
    ThetaLowerSegment 1991356672 1991487744 (6222798376387 / 3125) (99571371080959 / 50000) := by
  exact
    packedTile65536 1991356672 1991487744 14 6162 44624 31 _ _ (2141207 / 100000) (214121 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1991487744 :
    ThetaLowerSegment 1991487744 1991618816 (99571371080959 / 50000) (6223620333372 / 3125) := by
  exact
    packedTile65536 1991487744 1991618816 14 6122 44626 31 _ _ (2141213 / 100000) (66913 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1991618816 :
    ThetaLowerSegment 1991618816 1991749888 (6223620333372 / 3125) (49792256398641 / 25000) := by
  exact
    packedTile65536 1991618816 1991749888 14 6153 44627 31 _ _ (107061 / 5000) (2141223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1991749888 :
    ThetaLowerSegment 1991749888 1991880960 (49792256398641 / 25000) (99591008206353 / 50000) := by
  exact
    packedTile65536 1991749888 1991880960 14 6067 44629 31 _ _ (1070613 / 50000) (2141229 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1991880960 :
    ThetaLowerSegment 1991880960 1992012032 (99591008206353 / 50000)
      (199194994425919 / 100000) := by
  exact
    packedTile65536 1991880960 1992012032 14 6061 44630 31 _ _ (2141233 / 100000) (535309 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992012032 :
    ThetaLowerSegment 1992012032 1992143104 (199194994425919 / 100000)
      (199208109520919 / 100000) := by
  exact
    packedTile65536 1992012032 1992143104 14 6125 44631 31 _ _ (53531 / 2500) (2141243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992143104 :
    ThetaLowerSegment 1992143104 1992274176 (199208109520919 / 100000)
      (39844262488751 / 20000) := by
  exact
    packedTile65536 1992143104 1992274176 14 6166 44633 31 _ _ (1070623 / 50000) (2141249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992274176 :
    ThetaLowerSegment 1992274176 1992405248 (39844262488751 / 20000)
      (199234335544501 / 100000) := by
  exact
    packedTile65536 1992274176 1992405248 14 6082 44634 31 _ _ (2141253 / 100000) (267657 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992405248 :
    ThetaLowerSegment 1992405248 1992536320 (199234335544501 / 100000)
      (199247482874761 / 100000) := by
  exact
    packedTile65536 1992405248 1992536320 14 6140 44636 31 _ _ (2141259 / 100000) (1070631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992536320 :
    ThetaLowerSegment 1992536320 1992667392 (199247482874761 / 100000)
      (199260546738627 / 100000) := by
  exact
    packedTile65536 1992536320 1992667392 14 6101 44637 31 _ _ (1070633 / 50000) (2141269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992667392 :
    ThetaLowerSegment 1992667392 1992798464 (199260546738627 / 100000)
      (199273565672387 / 100000) := by
  exact
    packedTile65536 1992667392 1992798464 14 6080 44639 31 _ _ (267659 / 12500) (85651 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992798464 :
    ThetaLowerSegment 1992798464 1992929536 (199273565672387 / 100000)
      (49821752690807 / 25000) := by
  exact
    packedTile65536 1992798464 1992929536 14 6279 44640 31 _ _ (2141279 / 100000) (1070641 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1992929536 :
    ThetaLowerSegment 1992929536 1993060608 (49821752690807 / 25000) (49825048129961 / 25000) := by
  exact
    packedTile65536 1992929536 1993060608 14 6156 44642 31 _ _ (1070643 / 50000) (2141289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993060608 :
    ThetaLowerSegment 1993060608 1993191680 (49825048129961 / 25000) (2491414957327 / 1250) := by
  exact
    packedTile65536 1993060608 1993191680 14 6073 44643 31 _ _ (535323 / 25000) (428259 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993191680 :
    ThetaLowerSegment 1993191680 1993322752 (2491414957327 / 1250) (24915770536613 / 12500) := by
  exact
    packedTile65536 1993191680 1993322752 14 6056 44645 31 _ _ (2141299 / 100000) (1070651 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993322752 :
    ThetaLowerSegment 1993322752 1993339136 (24915770536613 / 12500) (99663855157557 / 50000) := by
  exact
    packedTile65536 1993322752 1993339136 11 722 44646 31 _ _ (428261 / 20000) (535327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1993339136 :
    ThetaLowerSegment 1993339136 1993341184 (99663855157557 / 50000) (99663955798939 / 50000) := by
  exact
    packedTile65536 1993339136 1993341184 8 94 44646 31 _ _ (1070653 / 50000) (2141309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1961341184_1993341184 :
    ThetaLowerSegment 1961341184 1993341184 (196127600570263 / 100000)
      (99663955798939 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1961341184 cell1961472256)
                  (ThetaLowerSegment.join cell1961603328 cell1961734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1961865472 cell1961996544)
                  (ThetaLowerSegment.join cell1962127616 cell1962258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1962389760 cell1962520832)
                  (ThetaLowerSegment.join cell1962651904 cell1962782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1962914048 cell1963045120)
                  (ThetaLowerSegment.join cell1963176192 cell1963307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1963438336 cell1963569408)
                  (ThetaLowerSegment.join cell1963700480 cell1963831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1963962624 cell1964093696)
                  (ThetaLowerSegment.join cell1964224768 cell1964355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1964486912 cell1964617984)
                  (ThetaLowerSegment.join cell1964749056 cell1964880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1965011200 cell1965142272)
                  (ThetaLowerSegment.join cell1965273344 cell1965404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1965535488 cell1965666560)
                  (ThetaLowerSegment.join cell1965797632 cell1965928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1966059776 cell1966190848)
                  (ThetaLowerSegment.join cell1966321920 cell1966452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1966584064 cell1966715136)
                  (ThetaLowerSegment.join cell1966846208 cell1966977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1967108352 cell1967239424)
                  (ThetaLowerSegment.join cell1967370496 cell1967501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1967632640 cell1967763712)
                  (ThetaLowerSegment.join cell1967894784 cell1968025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1968156928 cell1968288000)
                  (ThetaLowerSegment.join cell1968419072 cell1968550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1968681216 cell1968812288)
                  (ThetaLowerSegment.join cell1968943360 cell1969074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1969205504 cell1969336576)
                  (ThetaLowerSegment.join cell1969467648 cell1969598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1969729792 cell1969860864)
                  (ThetaLowerSegment.join cell1969991936 cell1970123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1970254080 cell1970385152)
                  (ThetaLowerSegment.join cell1970516224 cell1970647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1970778368 cell1970909440)
                  (ThetaLowerSegment.join cell1971040512 cell1971171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1971302656 cell1971433728)
                  (ThetaLowerSegment.join cell1971564800 cell1971695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1971826944 cell1971958016)
                  (ThetaLowerSegment.join cell1972089088 cell1972220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1972351232 cell1972482304)
                  (ThetaLowerSegment.join cell1972613376 cell1972744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1972875520 cell1973006592)
                  (ThetaLowerSegment.join cell1973137664 cell1973268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1973399808 cell1973530880)
                  (ThetaLowerSegment.join cell1973661952 cell1973793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1973924096 cell1974055168)
                  (ThetaLowerSegment.join cell1974186240 cell1974317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1974448384 cell1974579456)
                  (ThetaLowerSegment.join cell1974710528 cell1974841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1974972672 cell1975103744)
                  (ThetaLowerSegment.join cell1975234816 cell1975365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1975496960 cell1975628032)
                  (ThetaLowerSegment.join cell1975759104 cell1975890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1976021248 cell1976152320)
                  (ThetaLowerSegment.join cell1976283392 cell1976414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1976545536 cell1976676608)
                  (ThetaLowerSegment.join cell1976807680 cell1976938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1977069824 cell1977200896)
                  (ThetaLowerSegment.join cell1977331968 cell1977463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1977594112 cell1977725184)
                  (ThetaLowerSegment.join cell1977856256 cell1977987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1978118400 cell1978249472)
                  (ThetaLowerSegment.join cell1978380544 cell1978511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1978642688 cell1978773760)
                  (ThetaLowerSegment.join cell1978904832 cell1979035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1979166976 cell1979298048)
                  (ThetaLowerSegment.join cell1979429120 cell1979560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1979691264 cell1979822336)
                  (ThetaLowerSegment.join cell1979953408 cell1980084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1980215552 cell1980346624)
                  (ThetaLowerSegment.join cell1980477696 cell1980608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1980739840 cell1980870912)
                  (ThetaLowerSegment.join cell1981001984 cell1981133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1981264128 cell1981395200)
                  (ThetaLowerSegment.join cell1981526272 cell1981657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1981788416 cell1981919488)
                  (ThetaLowerSegment.join cell1982050560 cell1982181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1982312704 cell1982443776)
                  (ThetaLowerSegment.join cell1982574848 cell1982705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1982836992 cell1982968064)
                  (ThetaLowerSegment.join cell1983099136 cell1983230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1983361280 cell1983492352)
                  (ThetaLowerSegment.join cell1983623424 cell1983754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1983885568 cell1984016640)
                  (ThetaLowerSegment.join cell1984147712 cell1984278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1984409856 cell1984540928)
                  (ThetaLowerSegment.join cell1984672000 cell1984803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1984934144 cell1985065216)
                  (ThetaLowerSegment.join cell1985196288 cell1985327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1985458432 cell1985589504)
                  (ThetaLowerSegment.join cell1985720576 cell1985851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1985982720 cell1986113792)
                  (ThetaLowerSegment.join cell1986244864 cell1986375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1986507008 cell1986638080)
                  (ThetaLowerSegment.join cell1986769152 cell1986900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1987031296 cell1987162368)
                  (ThetaLowerSegment.join cell1987293440 cell1987424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1987555584 cell1987686656)
                  (ThetaLowerSegment.join cell1987817728 cell1987948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1988079872 cell1988210944)
                  (ThetaLowerSegment.join cell1988342016 cell1988473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1988604160 cell1988735232)
                  (ThetaLowerSegment.join cell1988866304 cell1988997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1989128448 cell1989259520)
                  (ThetaLowerSegment.join cell1989390592 cell1989521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1989652736 cell1989783808)
                  (ThetaLowerSegment.join cell1989914880 cell1990045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1990177024 cell1990308096)
                  (ThetaLowerSegment.join cell1990439168 cell1990570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1990701312 cell1990832384)
                  (ThetaLowerSegment.join cell1990963456 cell1991094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1991225600 cell1991356672)
                  (ThetaLowerSegment.join cell1991487744 cell1991618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1991749888 cell1991880960)
                  (ThetaLowerSegment.join cell1992012032 cell1992143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1992274176 cell1992405248)
                  (ThetaLowerSegment.join cell1992536320 cell1992667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1992798464 cell1992929536)
                (ThetaLowerSegment.join cell1993060608 cell1993191680))
              (ThetaLowerSegment.join cell1993322752 cell1993339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
