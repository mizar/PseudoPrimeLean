/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 1577341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell1545341184 :
    ThetaLowerSegment 1545341184 1545472256 (77265055344773 / 50000) (77271603900523 / 50000) := by
  exact
    packedTile65536 1545341184 1545472256 14 6190 39310 31 _ _ (42317 / 2000) (2115853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545472256 :
    ThetaLowerSegment 1545472256 1545603328 (77271603900523 / 50000) (38639055610901 / 25000) := by
  exact
    packedTile65536 1545472256 1545603328 14 6151 39312 31 _ _ (1057929 / 50000) (2115861 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545603328 :
    ThetaLowerSegment 1545603328 1545734400 (38639055610901 / 25000) (15456946353929 / 10000) := by
  exact
    packedTile65536 1545603328 1545734400 14 6258 39314 31 _ _ (2115867 / 100000) (211587 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545734400 :
    ThetaLowerSegment 1545734400 1545865472 (15456946353929 / 10000) (30916534589383 / 20000) := by
  exact
    packedTile65536 1545734400 1545865472 14 6243 39315 31 _ _ (16927 / 800) (1057939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545865472 :
    ThetaLowerSegment 1545865472 1545996544 (30916534589383 / 20000)
      (154595711017961 / 100000) := by
  exact
    packedTile65536 1545865472 1545996544 14 6162 39317 31 _ _ (2115883 / 100000) (1057943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1545996544 :
    ThetaLowerSegment 1545996544 1546127616 (154595711017961 / 100000)
      (154608922647609 / 100000) := by
  exact
    packedTile65536 1545996544 1546127616 14 6244 39319 31 _ _ (528973 / 25000) (423179 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1546127616 :
    ThetaLowerSegment 1546127616 1546258688 (154608922647609 / 100000)
      (154621977750609 / 100000) := by
  exact
    packedTile65536 1546127616 1546258688 14 6170 39320 31 _ _ (21159 / 1000) (2115903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1546258688 :
    ThetaLowerSegment 1546258688 1546389760 (154621977750609 / 100000) (7731763177161 / 5000) := by
  exact
    packedTile65536 1546258688 1546389760 14 6279 39322 31 _ _ (2115909 / 100000) (264489 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1546389760 :
    ThetaLowerSegment 1546389760 1546520832 (7731763177161 / 5000) (966553711377 / 625) := by
  exact
    packedTile65536 1546389760 1546520832 14 6300 39324 31 _ _ (2115917 / 100000) (26449 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1546520832 :
    ThetaLowerSegment 1546520832 1546651904 (966553711377 / 625) (77330831947611 / 50000) := by
  exact
    packedTile65536 1546520832 1546651904 14 6177 39325 31 _ _ (1057963 / 50000) (2115929 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1546651904 :
    ThetaLowerSegment 1546651904 1546782976 (77330831947611 / 50000) (19334326411921 / 12500) := by
  exact
    packedTile65536 1546651904 1546782976 14 6119 39327 31 _ _ (1057967 / 50000) (2115937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1546782976 :
    ThetaLowerSegment 1546782976 1546914048 (19334326411921 / 12500)
      (154687630692647 / 100000) := by
  exact
    packedTile65536 1546782976 1546914048 14 6153 39329 31 _ _ (2115943 / 100000) (1057973 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1546914048 :
    ThetaLowerSegment 1546914048 1547045120 (154687630692647 / 100000)
      (154700901937319 / 100000) := by
  exact
    packedTile65536 1546914048 1547045120 14 6272 39330 31 _ _ (2115951 / 100000) (1057977 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547045120 :
    ThetaLowerSegment 1547045120 1547176192 (154700901937319 / 100000)
      (154714029353159 / 100000) := by
  exact
    packedTile65536 1547045120 1547176192 14 6204 39332 31 _ _ (52899 / 2500) (2115963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547176192 :
    ThetaLowerSegment 1547176192 1547307264 (154714029353159 / 100000)
      (154727125079111 / 100000) := by
  exact
    packedTile65536 1547176192 1547307264 14 6189 39334 31 _ _ (66124 / 3125) (2115971 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547307264 :
    ThetaLowerSegment 1547307264 1547438336 (154727125079111 / 100000)
      (154740180657201 / 100000) := by
  exact
    packedTile65536 1547307264 1547438336 14 6170 39335 31 _ _ (2115977 / 100000) (105799 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547438336 :
    ThetaLowerSegment 1547438336 1547569408 (154740180657201 / 100000)
      (154753270140411 / 100000) := by
  exact
    packedTile65536 1547438336 1547569408 14 6186 39337 31 _ _ (423197 / 20000) (528997 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547569408 :
    ThetaLowerSegment 1547569408 1547700480 (154753270140411 / 100000)
      (154766490870923 / 100000) := by
  exact
    packedTile65536 1547569408 1547700480 14 6248 39339 31 _ _ (1057997 / 50000) (2115997 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547700480 :
    ThetaLowerSegment 1547700480 1547831552 (154766490870923 / 100000)
      (154779493703213 / 100000) := by
  exact
    packedTile65536 1547700480 1547831552 14 6145 39340 31 _ _ (1058001 / 50000) (423201 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547831552 :
    ThetaLowerSegment 1547831552 1547962624 (154779493703213 / 100000)
      (77396263107481 / 50000) := by
  exact
    packedTile65536 1547831552 1547962624 14 6159 39342 31 _ _ (2116011 / 100000) (1058007 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1547962624 :
    ThetaLowerSegment 1547962624 1548093696 (77396263107481 / 50000) (19350699872543 / 12500) := by
  exact
    packedTile65536 1547962624 1548093696 14 6178 39344 31 _ _ (2116019 / 100000) (1058011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548093696 :
    ThetaLowerSegment 1548093696 1548224768 (19350699872543 / 12500) (38704722438053 / 25000) := by
  exact
    packedTile65536 1548093696 1548224768 14 6281 39345 31 _ _ (529007 / 25000) (2116031 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548224768 :
    ThetaLowerSegment 1548224768 1548355840 (38704722438053 / 25000) (19354000353413 / 12500) := by
  exact
    packedTile65536 1548224768 1548355840 14 6197 39347 31 _ _ (529009 / 25000) (2116039 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548355840 :
    ThetaLowerSegment 1548355840 1548486912 (19354000353413 / 12500) (19355627591249 / 12500) := by
  exact
    packedTile65536 1548355840 1548486912 14 6152 39349 31 _ _ (529011 / 25000) (2116047 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548486912 :
    ThetaLowerSegment 1548486912 1548617984 (19355627591249 / 12500)
      (154858188927811 / 100000) := by
  exact
    packedTile65536 1548486912 1548617984 14 6223 39350 31 _ _ (2116053 / 100000) (264507 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548617984 :
    ThetaLowerSegment 1548617984 1548749056 (154858188927811 / 100000) (9679455855849 / 6250) := by
  exact
    packedTile65536 1548617984 1548749056 14 6193 39352 31 _ _ (2116061 / 100000) (66127 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548749056 :
    ThetaLowerSegment 1548749056 1548880128 (9679455855849 / 6250) (77442120962957 / 50000) := by
  exact
    packedTile65536 1548749056 1548880128 14 6119 39354 31 _ _ (211607 / 10000) (2116073 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1548880128 :
    ThetaLowerSegment 1548880128 1549011200 (77442120962957 / 50000) (38724341989437 / 25000) := by
  exact
    packedTile65536 1548880128 1549011200 14 6203 39355 31 _ _ (1058039 / 50000) (2116081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549011200 :
    ThetaLowerSegment 1549011200 1549142272 (38724341989437 / 25000) (77455199410747 / 50000) := by
  exact
    packedTile65536 1549011200 1549142272 14 6158 39357 31 _ _ (2116087 / 100000) (211609 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549142272 :
    ThetaLowerSegment 1549142272 1549273344 (77455199410747 / 50000) (77461746608677 / 50000) := by
  exact
    packedTile65536 1549142272 1549273344 14 6188 39359 31 _ _ (423219 / 20000) (1058049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549273344 :
    ThetaLowerSegment 1549273344 1549404416 (77461746608677 / 50000) (77468299124713 / 50000) := by
  exact
    packedTile65536 1549273344 1549404416 14 6193 39360 31 _ _ (264513 / 12500) (2116107 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549404416 :
    ThetaLowerSegment 1549404416 1549535488 (77468299124713 / 50000) (15494971179549 / 10000) := by
  exact
    packedTile65536 1549404416 1549535488 14 6197 39362 31 _ _ (132257 / 6250) (423223 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549535488 :
    ThetaLowerSegment 1549535488 1549666560 (15494971179549 / 10000)
      (154962723823519 / 100000) := by
  exact
    packedTile65536 1549535488 1549666560 14 6149 39364 31 _ _ (2116121 / 100000) (529031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549666560 :
    ThetaLowerSegment 1549666560 1549797632 (154962723823519 / 100000)
      (19372001903721 / 12500) := by
  exact
    packedTile65536 1549666560 1549797632 14 6281 39365 31 _ _ (2116129 / 100000) (529033 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549797632 :
    ThetaLowerSegment 1549797632 1549928704 (19372001903721 / 12500) (77494659694687 / 50000) := by
  exact
    packedTile65536 1549797632 1549928704 14 6287 39367 31 _ _ (1058069 / 50000) (2116141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1549928704 :
    ThetaLowerSegment 1549928704 1550059776 (77494659694687 / 50000) (77501113939987 / 50000) := by
  exact
    packedTile65536 1549928704 1550059776 14 6100 39369 31 _ _ (1058073 / 50000) (2116149 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550059776 :
    ThetaLowerSegment 1550059776 1550190848 (77501113939987 / 50000) (1937693146579 / 1250) := by
  exact
    packedTile65536 1550059776 1550190848 14 6249 39370 31 _ _ (1058077 / 50000) (2116157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550190848 :
    ThetaLowerSegment 1550190848 1550321920 (1937693146579 / 1250) (31005716503547 / 20000) := by
  exact
    packedTile65536 1550190848 1550321920 14 6205 39372 31 _ _ (2116163 / 100000) (1058083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550321920 :
    ThetaLowerSegment 1550321920 1550452992 (31005716503547 / 20000)
      (155041707010277 / 100000) := by
  exact
    packedTile65536 1550321920 1550452992 14 6202 39374 31 _ _ (2116171 / 100000) (1058087 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550452992 :
    ThetaLowerSegment 1550452992 1550584064 (155041707010277 / 100000)
      (155054808280657 / 100000) := by
  exact
    packedTile65536 1550452992 1550584064 14 6191 39375 31 _ _ (105809 / 5000) (2116183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550584064 :
    ThetaLowerSegment 1550584064 1550715136 (155054808280657 / 100000)
      (155068127567929 / 100000) := by
  exact
    packedTile65536 1550584064 1550715136 14 6294 39377 31 _ _ (529047 / 25000) (2116191 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550715136 :
    ThetaLowerSegment 1550715136 1550846208 (155068127567929 / 100000)
      (155081273383693 / 100000) := by
  exact
    packedTile65536 1550715136 1550846208 14 6212 39379 31 _ _ (2116197 / 100000) (10581 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550846208 :
    ThetaLowerSegment 1550846208 1550977280 (155081273383693 / 100000)
      (38773629677697 / 25000) := by
  exact
    packedTile65536 1550846208 1550977280 14 6259 39380 31 _ _ (423241 / 20000) (132263 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1550977280 :
    ThetaLowerSegment 1550977280 1551108352 (38773629677697 / 25000) (9694222426341 / 6250) := by
  exact
    packedTile65536 1550977280 1551108352 14 6162 39382 31 _ _ (1058107 / 50000) (2116217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1551108352 :
    ThetaLowerSegment 1551108352 1551239424 (9694222426341 / 6250) (38780194186017 / 25000) := by
  exact
    packedTile65536 1551108352 1551239424 14 6246 39384 31 _ _ (1058111 / 50000) (84649 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1551239424 :
    ThetaLowerSegment 1551239424 1551370496 (38780194186017 / 25000)
      (155133857167879 / 100000) := by
  exact
    packedTile65536 1551239424 1551370496 14 6181 39385 31 _ _ (2116231 / 100000) (1058117 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1551370496 :
    ThetaLowerSegment 1551370496 1551501568 (155133857167879 / 100000)
      (31029397262927 / 20000) := by
  exact
    packedTile65536 1551370496 1551501568 14 6204 39387 31 _ _ (2116239 / 100000) (1058121 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1551501568 :
    ThetaLowerSegment 1551501568 1551632640 (31029397262927 / 20000)
      (155159992768697 / 100000) := by
  exact
    packedTile65536 1551501568 1551632640 14 6146 39389 31 _ _ (2116247 / 100000) (1693 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1551632640 :
    ThetaLowerSegment 1551632640 1551763712 (155159992768697 / 100000)
      (31034626097189 / 20000) := by
  exact
    packedTile65536 1551632640 1551763712 14 6208 39390 31 _ _ (66133 / 3125) (2116259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1551763712 :
    ThetaLowerSegment 1551763712 1551894784 (31034626097189 / 20000)
      (155186276717913 / 100000) := by
  exact
    packedTile65536 1551763712 1551894784 14 6212 39392 31 _ _ (264533 / 12500) (2116267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1551894784 :
    ThetaLowerSegment 1551894784 1552025856 (155186276717913 / 100000)
      (155199355285053 / 100000) := by
  exact
    packedTile65536 1551894784 1552025856 14 6180 39394 31 _ _ (2116273 / 100000) (529069 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552025856 :
    ThetaLowerSegment 1552025856 1552156928 (155199355285053 / 100000)
      (155212366180641 / 100000) := by
  exact
    packedTile65536 1552025856 1552156928 14 6148 39395 31 _ _ (2116281 / 100000) (529071 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552156928 :
    ThetaLowerSegment 1552156928 1552288000 (155212366180641 / 100000)
      (155225377131561 / 100000) := by
  exact
    packedTile65536 1552156928 1552288000 14 6148 39397 31 _ _ (211629 / 10000) (2116293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552288000 :
    ThetaLowerSegment 1552288000 1552419072 (155225377131561 / 100000)
      (155238457969499 / 100000) := by
  exact
    packedTile65536 1552288000 1552419072 14 6181 39399 31 _ _ (1058149 / 50000) (2116301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552419072 :
    ThetaLowerSegment 1552419072 1552550144 (155238457969499 / 100000)
      (155251604468583 / 100000) := by
  exact
    packedTile65536 1552419072 1552550144 14 6212 39400 31 _ _ (2116307 / 100000) (211631 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552550144 :
    ThetaLowerSegment 1552550144 1552681216 (155251604468583 / 100000)
      (38816180876317 / 25000) := by
  exact
    packedTile65536 1552550144 1552681216 14 6199 39402 31 _ _ (423263 / 20000) (1058159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552681216 :
    ThetaLowerSegment 1552681216 1552812288 (38816180876317 / 25000) (77638877911151 / 50000) := by
  exact
    packedTile65536 1552681216 1552812288 14 6158 39404 31 _ _ (2116323 / 100000) (1058163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552812288 :
    ThetaLowerSegment 1552812288 1552943360 (77638877911151 / 50000) (77645539066121 / 50000) := by
  exact
    packedTile65536 1552812288 1552943360 14 6295 39405 31 _ _ (529083 / 25000) (423267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1552943360 :
    ThetaLowerSegment 1552943360 1553074432 (77645539066121 / 50000) (77652016124691 / 50000) := by
  exact
    packedTile65536 1552943360 1553074432 14 6121 39407 31 _ _ (105817 / 5000) (2116343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553074432 :
    ThetaLowerSegment 1553074432 1553205504 (77652016124691 / 50000)
      (155317138798739 / 100000) := by
  exact
    packedTile65536 1553074432 1553205504 14 6193 39409 31 _ _ (2116349 / 100000) (66136 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553205504 :
    ThetaLowerSegment 1553205504 1553336576 (155317138798739 / 100000)
      (155330196721429 / 100000) := by
  exact
    packedTile65536 1553205504 1553336576 14 6170 39410 31 _ _ (2116357 / 100000) (52909 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553336576 :
    ThetaLowerSegment 1553336576 1553467648 (155330196721429 / 100000)
      (155343445172589 / 100000) := by
  exact
    packedTile65536 1553336576 1553467648 14 6260 39412 31 _ _ (1058183 / 50000) (2116369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553467648 :
    ThetaLowerSegment 1553467648 1553598720 (155343445172589 / 100000)
      (155356509549291 / 100000) := by
  exact
    packedTile65536 1553467648 1553598720 14 6173 39414 31 _ _ (1058187 / 50000) (2116377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553598720 :
    ThetaLowerSegment 1553598720 1553729792 (155356509549291 / 100000)
      (155369523182209 / 100000) := by
  exact
    packedTile65536 1553598720 1553729792 14 6149 39415 31 _ _ (1058191 / 50000) (423277 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553729792 :
    ThetaLowerSegment 1553729792 1553860864 (155369523182209 / 100000)
      (155382665970319 / 100000) := by
  exact
    packedTile65536 1553729792 1553860864 14 6210 39417 31 _ _ (2116391 / 100000) (1058197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553860864 :
    ThetaLowerSegment 1553860864 1553991936 (155382665970319 / 100000)
      (155395872300079 / 100000) := by
  exact
    packedTile65536 1553860864 1553991936 14 6240 39419 31 _ _ (2116399 / 100000) (1058201 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1553991936 :
    ThetaLowerSegment 1553991936 1554123008 (155395872300079 / 100000)
      (31081784837643 / 20000) := by
  exact
    packedTile65536 1553991936 1554123008 14 6167 39420 31 _ _ (264551 / 12500) (2116411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1554123008 :
    ThetaLowerSegment 1554123008 1554254080 (31081784837643 / 20000)
      (155422100994231 / 100000) := by
  exact
    packedTile65536 1554123008 1554254080 14 6226 39422 31 _ _ (66138 / 3125) (2116419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1554254080 :
    ThetaLowerSegment 1554254080 1554385152 (155422100994231 / 100000) (9714692035191 / 6250) := by
  exact
    packedTile65536 1554254080 1554385152 14 6129 39424 31 _ _ (84657 / 4000) (529107 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1554385152 :
    ThetaLowerSegment 1554385152 1554516224 (9714692035191 / 6250) (155448298152873 / 100000) := by
  exact
    packedTile65536 1554385152 1554516224 14 6249 39425 31 _ _ (2116433 / 100000) (529109 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1554516224 :
    ThetaLowerSegment 1554516224 1554647296 (155448298152873 / 100000) (6218453078793 / 4000) := by
  exact
    packedTile65536 1554516224 1554647296 14 6156 39427 31 _ _ (1058221 / 50000) (423289 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1554647296 :
    ThetaLowerSegment 1554647296 1554778368 (6218453078793 / 4000) (6218979058947 / 4000) := by
  exact
    packedTile65536 1554647296 1554778368 14 6213 39429 31 _ _ (42329 / 2000) (2116453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1554778368 :
    ThetaLowerSegment 1554778368 1554909440 (6218979058947 / 4000) (155487558300573 / 100000) := by
  exact
    packedTile65536 1554778368 1554909440 14 6181 39430 31 _ _ (1058229 / 50000) (2116461 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1554909440 :
    ThetaLowerSegment 1554909440 1555040512 (155487558300573 / 100000) (4859397915864 / 3125) := by
  exact
    packedTile65536 1554909440 1555040512 14 6225 39432 31 _ _ (2116467 / 100000) (211647 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555040512 :
    ThetaLowerSegment 1555040512 1555171584 (4859397915864 / 3125) (4859806395539 / 3125) := by
  exact
    packedTile65536 1555040512 1555171584 14 6176 39434 31 _ _ (84659 / 4000) (1058239 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555171584 :
    ThetaLowerSegment 1555171584 1555302656 (4859806395539 / 3125) (38881713195277 / 25000) := by
  exact
    packedTile65536 1555171584 1555302656 14 6165 39435 31 _ _ (529121 / 25000) (2116487 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555302656 :
    ThetaLowerSegment 1555302656 1555433728 (38881713195277 / 25000) (19442513546313 / 12500) := by
  exact
    packedTile65536 1555302656 1555433728 14 6263 39437 31 _ _ (529123 / 25000) (423299 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555433728 :
    ThetaLowerSegment 1555433728 1555564800 (19442513546313 / 12500) (38888271688659 / 25000) := by
  exact
    packedTile65536 1555433728 1555564800 14 6132 39438 31 _ _ (2116501 / 100000) (264563 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555564800 :
    ThetaLowerSegment 1555564800 1555695872 (38888271688659 / 25000)
      (155566372081629 / 100000) := by
  exact
    packedTile65536 1555564800 1555695872 14 6277 39440 31 _ _ (2116509 / 100000) (66141 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555695872 :
    ThetaLowerSegment 1555695872 1555826944 (155566372081629 / 100000) (1944741114811 / 1250) := by
  exact
    packedTile65536 1555695872 1555826944 14 6103 39442 31 _ _ (2116517 / 100000) (52913 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555826944 :
    ThetaLowerSegment 1555826944 1555958016 (1944741114811 / 1250) (3111845904743 / 2000) := by
  exact
    packedTile65536 1555826944 1555958016 14 6145 39443 31 _ _ (1058263 / 50000) (2116529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1555958016 :
    ThetaLowerSegment 1555958016 1556089088 (3111845904743 / 2000) (77802679242499 / 50000) := by
  exact
    packedTile65536 1555958016 1556089088 14 6172 39445 31 _ _ (1058267 / 50000) (2116537 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556089088 :
    ThetaLowerSegment 1556089088 1556220160 (77802679242499 / 50000) (3890464883623 / 2500) := by
  exact
    packedTile65536 1556089088 1556220160 14 6254 39447 31 _ _ (2116543 / 100000) (1058273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556220160 :
    ThetaLowerSegment 1556220160 1556351232 (3890464883623 / 2500) (77815767968867 / 50000) := by
  exact
    packedTile65536 1556220160 1556351232 14 6114 39448 31 _ _ (2116551 / 100000) (1058277 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556351232 :
    ThetaLowerSegment 1556351232 1556482304 (77815767968867 / 50000) (77822329301767 / 50000) := by
  exact
    packedTile65536 1556351232 1556482304 14 6200 39450 31 _ _ (2116559 / 100000) (1058281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556482304 :
    ThetaLowerSegment 1556482304 1556613376 (77822329301767 / 50000) (77828899128839 / 50000) := by
  exact
    packedTile65536 1556482304 1556613376 14 6208 39452 31 _ _ (264571 / 12500) (2116571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556613376 :
    ThetaLowerSegment 1556613376 1556744448 (77828899128839 / 50000) (77835554702071 / 50000) := by
  exact
    packedTile65536 1556613376 1556744448 14 6289 39453 31 _ _ (66143 / 3125) (2116579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556744448 :
    ThetaLowerSegment 1556744448 1556875520 (77835554702071 / 50000) (77842128815081 / 50000) := by
  exact
    packedTile65536 1556744448 1556875520 14 6212 39455 31 _ _ (423317 / 20000) (529147 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1556875520 :
    ThetaLowerSegment 1556875520 1557006592 (77842128815081 / 50000) (9731082842209 / 6250) := by
  exact
    packedTile65536 1556875520 1557006592 14 6174 39457 31 _ _ (2116593 / 100000) (529149 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557006592 :
    ThetaLowerSegment 1557006592 1557137664 (9731082842209 / 6250) (77855165997317 / 50000) := by
  exact
    packedTile65536 1557006592 1557137664 14 6145 39458 31 _ _ (1058301 / 50000) (423321 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557137664 :
    ThetaLowerSegment 1557137664 1557268736 (77855165997317 / 50000) (77861727488317 / 50000) := by
  exact
    packedTile65536 1557137664 1557268736 14 6200 39460 31 _ _ (211661 / 10000) (2116613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557268736 :
    ThetaLowerSegment 1557268736 1557399808 (77861727488317 / 50000) (38934113281943 / 25000) := by
  exact
    packedTile65536 1557268736 1557399808 14 6141 39462 31 _ _ (1058309 / 50000) (2116621 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557399808 :
    ThetaLowerSegment 1557399808 1557530880 (38934113281943 / 25000)
      (155749612197831 / 100000) := by
  exact
    packedTile65536 1557399808 1557530880 14 6217 39463 31 _ _ (2116627 / 100000) (211663 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557530880 :
    ThetaLowerSegment 1557530880 1557661952 (155749612197831 / 100000)
      (77881360259193 / 50000) := by
  exact
    packedTile65536 1557530880 1557661952 14 6193 39465 31 _ _ (423327 / 20000) (1058319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557661952 :
    ThetaLowerSegment 1557661952 1557793024 (77881360259193 / 50000) (77887925030559 / 50000) := by
  exact
    packedTile65536 1557661952 1557793024 14 6203 39467 31 _ _ (529161 / 25000) (2116647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557793024 :
    ThetaLowerSegment 1557793024 1557924096 (77887925030559 / 50000) (77894512051583 / 50000) := by
  exact
    packedTile65536 1557793024 1557924096 14 6224 39468 31 _ _ (529163 / 25000) (423331 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1557924096 :
    ThetaLowerSegment 1557924096 1558055168 (77894512051583 / 50000) (77900955167667 / 50000) := by
  exact
    packedTile65536 1557924096 1558055168 14 6088 39470 31 _ _ (2116661 / 100000) (264583 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558055168 :
    ThetaLowerSegment 1558055168 1558186240 (77900955167667 / 50000)
      (155815078133183 / 100000) := by
  exact
    packedTile65536 1558055168 1558186240 14 6221 39472 31 _ _ (2116669 / 100000) (66146 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558186240 :
    ThetaLowerSegment 1558186240 1558317312 (155815078133183 / 100000) (7791410182363 / 5000) := by
  exact
    packedTile65536 1558186240 1558317312 14 6201 39473 31 _ _ (2116677 / 100000) (52917 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558317312 :
    ThetaLowerSegment 1558317312 1558448384 (7791410182363 / 5000) (77920687892119 / 50000) := by
  exact
    packedTile65536 1558317312 1558448384 14 6223 39475 31 _ _ (1058343 / 50000) (2116689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558448384 :
    ThetaLowerSegment 1558448384 1558579456 (77920687892119 / 50000) (7792707289957 / 5000) := by
  exact
    packedTile65536 1558448384 1558579456 14 6033 39477 31 _ _ (1058347 / 50000) (2116697 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558579456 :
    ThetaLowerSegment 1558579456 1558710528 (7792707289957 / 5000) (77933704530069 / 50000) := by
  exact
    packedTile65536 1558579456 1558710528 14 6266 39478 31 _ _ (2116703 / 100000) (1058353 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558710528 :
    ThetaLowerSegment 1558710528 1558841600 (77933704530069 / 50000) (779403107851 / 500) := by
  exact
    packedTile65536 1558710528 1558841600 14 6242 39480 31 _ _ (2116711 / 100000) (1058357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558841600 :
    ThetaLowerSegment 1558841600 1558972672 (779403107851 / 500) (77946853563529 / 50000) := by
  exact
    packedTile65536 1558841600 1558972672 14 6182 39482 31 _ _ (2116719 / 100000) (1058361 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1558972672 :
    ThetaLowerSegment 1558972672 1559103744 (77946853563529 / 50000) (77953521256729 / 50000) := by
  exact
    packedTile65536 1558972672 1559103744 14 6300 39483 31 _ _ (264591 / 12500) (2116731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1559103744 :
    ThetaLowerSegment 1559103744 1559234816 (77953521256729 / 50000) (3118404256897 / 2000) := by
  exact
    packedTile65536 1559103744 1559234816 14 6222 39485 31 _ _ (66148 / 3125) (2116739 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1559234816 :
    ThetaLowerSegment 1559234816 1559365888 (3118404256897 / 2000) (31186660135837 / 20000) := by
  exact
    packedTile65536 1559234816 1559365888 14 6183 39487 31 _ _ (423349 / 20000) (529187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1559365888 :
    ThetaLowerSegment 1559365888 1559496960 (31186660135837 / 20000) (77973170997209 / 50000) := by
  exact
    packedTile65536 1559365888 1559496960 14 6161 39488 31 _ _ (2116753 / 100000) (529189 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1559496960 :
    ThetaLowerSegment 1559496960 1559628032 (77973170997209 / 50000)
      (155959387592461 / 100000) := by
  exact
    packedTile65536 1559496960 1559628032 14 6163 39490 31 _ _ (2116761 / 100000) (529191 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1559628032 :
    ThetaLowerSegment 1559628032 1559759104 (155959387592461 / 100000)
      (155972532734161 / 100000) := by
  exact
    packedTile65536 1559628032 1559759104 14 6210 39492 31 _ _ (211677 / 10000) (2116773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1559759104 :
    ThetaLowerSegment 1559759104 1559890176 (155972532734161 / 100000)
      (155985637706759 / 100000) := by
  exact
    packedTile65536 1559759104 1559890176 14 6191 39493 31 _ _ (1058389 / 50000) (2116781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1559890176 :
    ThetaLowerSegment 1559890176 1560021248 (155985637706759 / 100000)
      (77999369250751 / 50000) := by
  exact
    packedTile65536 1559890176 1560021248 14 6189 39495 31 _ _ (2116787 / 100000) (211679 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560021248 :
    ThetaLowerSegment 1560021248 1560152320 (77999369250751 / 50000) (78005893212941 / 50000) := by
  exact
    packedTile65536 1560021248 1560152320 14 6164 39497 31 _ _ (423359 / 20000) (1058399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560152320 :
    ThetaLowerSegment 1560152320 1560283392 (78005893212941 / 50000)
      (156024980458981 / 100000) := by
  exact
    packedTile65536 1560152320 1560283392 14 6233 39498 31 _ _ (2116803 / 100000) (1058403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560283392 :
    ThetaLowerSegment 1560283392 1560414464 (156024980458981 / 100000)
      (31207613318153 / 20000) := by
  exact
    packedTile65536 1560283392 1560414464 14 6182 39500 31 _ _ (529203 / 25000) (423363 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560414464 :
    ThetaLowerSegment 1560414464 1560545536 (31207613318153 / 20000) (31210189488093 / 20000) := by
  exact
    packedTile65536 1560414464 1560545536 14 6085 39502 31 _ _ (105841 / 5000) (2116823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560545536 :
    ThetaLowerSegment 1560545536 1560676608 (31210189488093 / 20000)
      (156064126817819 / 100000) := by
  exact
    packedTile65536 1560545536 1560676608 14 6226 39503 31 _ _ (2116829 / 100000) (66151 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560676608 :
    ThetaLowerSegment 1560676608 1560807680 (156064126817819 / 100000)
      (19509627029789 / 12500) := by
  exact
    packedTile65536 1560676608 1560807680 14 6089 39505 31 _ _ (2116837 / 100000) (52921 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560807680 :
    ThetaLowerSegment 1560807680 1560938752 (19509627029789 / 12500) (39022545753553 / 25000) := by
  exact
    packedTile65536 1560807680 1560938752 14 6220 39507 31 _ _ (423369 / 20000) (132303 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1560938752 :
    ThetaLowerSegment 1560938752 1561069824 (39022545753553 / 25000) (78051601891583 / 50000) := by
  exact
    packedTile65536 1560938752 1561069824 14 6151 39508 31 _ _ (1058427 / 50000) (2116857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561069824 :
    ThetaLowerSegment 1561069824 1561200896 (78051601891583 / 50000) (19514546068493 / 12500) := by
  exact
    packedTile65536 1561069824 1561200896 14 6219 39510 31 _ _ (1058431 / 50000) (423373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561200896 :
    ThetaLowerSegment 1561200896 1561331968 (19514546068493 / 12500)
      (156129376720239 / 100000) := by
  exact
    packedTile65536 1561200896 1561331968 14 6145 39512 31 _ _ (2116871 / 100000) (1058437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561331968 :
    ThetaLowerSegment 1561331968 1561463040 (156129376720239 / 100000)
      (156142471733733 / 100000) := by
  exact
    packedTile65536 1561331968 1561463040 14 6186 39513 31 _ _ (2116879 / 100000) (1058441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561463040 :
    ThetaLowerSegment 1561463040 1561594112 (156142471733733 / 100000)
      (156155549861619 / 100000) := by
  exact
    packedTile65536 1561463040 1561594112 14 6178 39515 31 _ _ (2116887 / 100000) (211689 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561594112 :
    ThetaLowerSegment 1561594112 1561725184 (156155549861619 / 100000)
      (156168579356499 / 100000) := by
  exact
    packedTile65536 1561594112 1561725184 14 6155 39517 31 _ _ (66153 / 3125) (2116899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561725184 :
    ThetaLowerSegment 1561725184 1561856256 (156168579356499 / 100000)
      (156181594082291 / 100000) := by
  exact
    packedTile65536 1561725184 1561856256 14 6148 39518 31 _ _ (264613 / 12500) (2116907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561856256 :
    ThetaLowerSegment 1561856256 1561987328 (156181594082291 / 100000)
      (39048642160517 / 25000) := by
  exact
    packedTile65536 1561856256 1561987328 14 6129 39520 31 _ _ (2116913 / 100000) (529229 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1561987328 :
    ThetaLowerSegment 1561987328 1562118400 (39048642160517 / 25000) (78103831957687 / 50000) := by
  exact
    packedTile65536 1561987328 1562118400 14 6186 39521 31 _ _ (2116921 / 100000) (529231 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1562118400 :
    ThetaLowerSegment 1562118400 1562249472 (78103831957687 / 50000) (78110343631291 / 50000) := by
  exact
    packedTile65536 1562118400 1562249472 14 6152 39523 31 _ _ (2116929 / 100000) (529233 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1562249472 :
    ThetaLowerSegment 1562249472 1562380544 (78110343631291 / 50000) (78116904022153 / 50000) := by
  exact
    packedTile65536 1562249472 1562380544 14 6198 39525 31 _ _ (1058469 / 50000) (2116941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1562380544 :
    ThetaLowerSegment 1562380544 1562511616 (78116904022153 / 50000) (78123525829241 / 50000) := by
  exact
    packedTile65536 1562380544 1562511616 14 6256 39526 31 _ _ (1058473 / 50000) (2116949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1562511616 :
    ThetaLowerSegment 1562511616 1562642688 (78123525829241 / 50000) (78130054518461 / 50000) := by
  exact
    packedTile65536 1562511616 1562642688 14 6168 39528 31 _ _ (423391 / 20000) (1058479 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1562642688 :
    ThetaLowerSegment 1562642688 1562773760 (78130054518461 / 50000) (31254613393489 / 20000) := by
  exact
    packedTile65536 1562642688 1562773760 14 6121 39530 31 _ _ (2116963 / 100000) (1058483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1562773760 :
    ThetaLowerSegment 1562773760 1562904832 (31254613393489 / 20000)
      (156286217591297 / 100000) := by
  exact
    packedTile65536 1562773760 1562904832 14 6212 39531 31 _ _ (2116971 / 100000) (1058487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1562904832 :
    ThetaLowerSegment 1562904832 1563035904 (156286217591297 / 100000)
      (156299232784337 / 100000) := by
  exact
    packedTile65536 1562904832 1563035904 14 6148 39533 31 _ _ (105849 / 5000) (2116983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563035904 :
    ThetaLowerSegment 1563035904 1563166976 (156299232784337 / 100000)
      (156312260728489 / 100000) := by
  exact
    packedTile65536 1563035904 1563166976 14 6154 39535 31 _ _ (529247 / 25000) (2116991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563166976 :
    ThetaLowerSegment 1563166976 1563298048 (156312260728489 / 100000)
      (156325216744009 / 100000) := by
  exact
    packedTile65536 1563166976 1563298048 14 6120 39536 31 _ _ (529249 / 25000) (2116999 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563298048 :
    ThetaLowerSegment 1563298048 1563429120 (156325216744009 / 100000) (4885574979192 / 3125) := by
  exact
    packedTile65536 1563298048 1563429120 14 6227 39538 31 _ _ (423401 / 20000) (132313 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563429120 :
    ThetaLowerSegment 1563429120 1563560192 (4885574979192 / 3125) (156351662420589 / 100000) := by
  exact
    packedTile65536 1563429120 1563560192 14 6265 39540 31 _ _ (2117013 / 100000) (264627 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563560192 :
    ThetaLowerSegment 1563560192 1563691264 (156351662420589 / 100000)
      (156364798542099 / 100000) := by
  exact
    packedTile65536 1563560192 1563691264 14 6205 39541 31 _ _ (1058511 / 50000) (84681 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563691264 :
    ThetaLowerSegment 1563691264 1563822336 (156364798542099 / 100000)
      (156377945298399 / 100000) := by
  exact
    packedTile65536 1563691264 1563822336 14 6210 39543 31 _ _ (211703 / 10000) (2117033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563822336 :
    ThetaLowerSegment 1563822336 1563953408 (156377945298399 / 100000)
      (156391094221417 / 100000) := by
  exact
    packedTile65536 1563822336 1563953408 14 6211 39545 31 _ _ (1058519 / 50000) (2117041 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1563953408 :
    ThetaLowerSegment 1563953408 1564084480 (156391094221417 / 100000) (1564041966253 / 1000) := by
  exact
    packedTile65536 1563953408 1564084480 14 6189 39546 31 _ _ (2117047 / 100000) (42341 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564084480 :
    ThetaLowerSegment 1564084480 1564215552 (1564041966253 / 1000) (15641715723601 / 10000) := by
  exact
    packedTile65536 1564084480 1564215552 14 6122 39548 31 _ _ (423411 / 20000) (1058529 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564215552 :
    ThetaLowerSegment 1564215552 1564346624 (15641715723601 / 10000) (15643043122729 / 10000) := by
  exact
    packedTile65536 1564215552 1564346624 14 6270 39550 31 _ _ (264633 / 12500) (2117067 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564346624 :
    ThetaLowerSegment 1564346624 1564477696 (15643043122729 / 10000) (78221733019797 / 50000) := by
  exact
    packedTile65536 1564346624 1564477696 14 6157 39551 31 _ _ (132317 / 6250) (84683 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564477696 :
    ThetaLowerSegment 1564477696 1564608768 (78221733019797 / 50000) (78228237748097 / 50000) := by
  exact
    packedTile65536 1564477696 1564608768 14 6145 39553 31 _ _ (52927 / 2500) (2117083 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564608768 :
    ThetaLowerSegment 1564608768 1564739840 (78228237748097 / 50000) (15646935586567 / 10000) := by
  exact
    packedTile65536 1564608768 1564739840 14 6084 39555 31 _ _ (2117089 / 100000) (529273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564739840 :
    ThetaLowerSegment 1564739840 1564870912 (15646935586567 / 10000) (78241215528371 / 50000) := by
  exact
    packedTile65536 1564739840 1564870912 14 6176 39556 31 _ _ (2117097 / 100000) (21171 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1564870912 :
    ThetaLowerSegment 1564870912 1565001984 (78241215528371 / 50000)
      (156495444901177 / 100000) := by
  exact
    packedTile65536 1564870912 1565001984 14 6147 39558 31 _ _ (423421 / 20000) (529277 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565001984 :
    ThetaLowerSegment 1565001984 1565133056 (156495444901177 / 100000)
      (156508513845899 / 100000) := by
  exact
    packedTile65536 1565001984 1565133056 14 6173 39560 31 _ _ (1058557 / 50000) (2117117 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565133056 :
    ThetaLowerSegment 1565133056 1565264128 (156508513845899 / 100000)
      (156521703515959 / 100000) := by
  exact
    packedTile65536 1565133056 1565264128 14 6230 39561 31 _ _ (1058561 / 50000) (16937 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565264128 :
    ThetaLowerSegment 1565264128 1565395200 (156521703515959 / 100000)
      (156534901710613 / 100000) := by
  exact
    packedTile65536 1565264128 1565395200 14 6234 39563 31 _ _ (2117131 / 100000) (1058567 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565395200 :
    ThetaLowerSegment 1565395200 1565526272 (156534901710613 / 100000)
      (78273983287691 / 50000) := by
  exact
    packedTile65536 1565395200 1565526272 14 6171 39565 31 _ _ (2117139 / 100000) (1058571 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565526272 :
    ThetaLowerSegment 1565526272 1565657344 (78273983287691 / 50000) (78280495631863 / 50000) := by
  exact
    packedTile65536 1565526272 1565657344 14 6152 39566 31 _ _ (2117147 / 100000) (42343 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565657344 :
    ThetaLowerSegment 1565657344 1565788416 (78280495631863 / 50000) (78287130798767 / 50000) := by
  exact
    packedTile65536 1565657344 1565788416 14 6268 39568 31 _ _ (529289 / 25000) (2117159 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565788416 :
    ThetaLowerSegment 1565788416 1565919488 (78287130798767 / 50000) (78293633667993 / 50000) := by
  exact
    packedTile65536 1565788416 1565919488 14 6143 39570 31 _ _ (529291 / 25000) (2117167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1565919488 :
    ThetaLowerSegment 1565919488 1566050560 (78293633667993 / 50000) (15660048272361 / 10000) := by
  exact
    packedTile65536 1565919488 1566050560 14 6242 39571 31 _ _ (529293 / 25000) (84687 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566050560 :
    ThetaLowerSegment 1566050560 1566181632 (15660048272361 / 10000) (78306791919819 / 50000) := by
  exact
    packedTile65536 1566050560 1566181632 14 6188 39573 31 _ _ (2117181 / 100000) (66162 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566181632 :
    ThetaLowerSegment 1566181632 1566312704 (78306791919819 / 50000)
      (156626479637837 / 100000) := by
  exact
    packedTile65536 1566181632 1566312704 14 6091 39575 31 _ _ (2117189 / 100000) (264649 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566312704 :
    ThetaLowerSegment 1566312704 1566443776 (156626479637837 / 100000)
      (156639527929111 / 100000) := by
  exact
    packedTile65536 1566312704 1566443776 14 6163 39576 31 _ _ (1058599 / 50000) (2117201 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566443776 :
    ThetaLowerSegment 1566443776 1566574848 (156639527929111 / 100000)
      (156652696950431 / 100000) := by
  exact
    packedTile65536 1566443776 1566574848 14 6220 39578 31 _ _ (1058603 / 50000) (2117209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566574848 :
    ThetaLowerSegment 1566574848 1566705920 (156652696950431 / 100000)
      (156665861787083 / 100000) := by
  exact
    packedTile65536 1566574848 1566705920 14 6218 39579 31 _ _ (1058607 / 50000) (2117217 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566705920 :
    ThetaLowerSegment 1566705920 1566836992 (156665861787083 / 100000)
      (78339529219021 / 50000) := by
  exact
    packedTile65536 1566705920 1566836992 14 6233 39581 31 _ _ (2117223 / 100000) (1058613 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566836992 :
    ThetaLowerSegment 1566836992 1566968064 (78339529219021 / 50000)
      (156692178918549 / 100000) := by
  exact
    packedTile65536 1566836992 1566968064 14 6197 39583 31 _ _ (2117231 / 100000) (1058617 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1566968064 :
    ThetaLowerSegment 1566968064 1567099136 (156692178918549 / 100000)
      (156705318503783 / 100000) := by
  exact
    packedTile65536 1566968064 1567099136 14 6206 39584 31 _ _ (2117239 / 100000) (1058621 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1567099136 :
    ThetaLowerSegment 1567099136 1567230208 (156705318503783 / 100000)
      (156718640228199 / 100000) := by
  exact
    packedTile65536 1567099136 1567230208 14 6292 39586 31 _ _ (66164 / 3125) (2117251 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1567230208 :
    ThetaLowerSegment 1567230208 1567361280 (156718640228199 / 100000)
      (31346324224947 / 20000) := by
  exact
    packedTile65536 1567230208 1567361280 14 6131 39588 31 _ _ (264657 / 12500) (2117259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1567361280 :
    ThetaLowerSegment 1567361280 1567492352 (31346324224947 / 20000) (31349008915699 / 20000) := by
  exact
    packedTile65536 1567361280 1567492352 14 6340 39589 31 _ _ (132329 / 6250) (2117267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1567492352 :
    ThetaLowerSegment 1567492352 1567623424 (31349008915699 / 20000)
      (156758078511083 / 100000) := by
  exact
    packedTile65536 1567492352 1567623424 14 6156 39591 31 _ _ (2117273 / 100000) (529319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1567623424 :
    ThetaLowerSegment 1567623424 1567754496 (156758078511083 / 100000) (9798193604497 / 6250) := by
  exact
    packedTile65536 1567623424 1567754496 14 6149 39593 31 _ _ (2117281 / 100000) (529321 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1567754496 :
    ThetaLowerSegment 1567754496 1567885568 (9798193604497 / 6250) (78392115610911 / 50000) := by
  exact
    packedTile65536 1567754496 1567885568 14 6203 39594 31 _ _ (211729 / 10000) (2117293 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1567885568 :
    ThetaLowerSegment 1567885568 1568016640 (78392115610911 / 50000) (9799821274233 / 6250) := by
  exact
    packedTile65536 1567885568 1568016640 14 6097 39596 31 _ _ (1058649 / 50000) (2117301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568016640 :
    ThetaLowerSegment 1568016640 1568147712 (9799821274233 / 6250) (78405105258833 / 50000) := by
  exact
    packedTile65536 1568016640 1568147712 14 6173 39598 31 _ _ (1058653 / 50000) (2117309 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568147712 :
    ThetaLowerSegment 1568147712 1568278784 (78405105258833 / 50000)
      (156823297641681 / 100000) := by
  exact
    packedTile65536 1568147712 1568278784 14 6181 39599 31 _ _ (423463 / 20000) (1058659 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568278784 :
    ThetaLowerSegment 1568278784 1568409856 (156823297641681 / 100000)
      (31367267223343 / 20000) := by
  exact
    packedTile65536 1568278784 1568409856 14 6158 39601 31 _ _ (2117323 / 100000) (1058663 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568409856 :
    ThetaLowerSegment 1568409856 1568540928 (31367267223343 / 20000)
      (156849412752971 / 100000) := by
  exact
    packedTile65536 1568409856 1568540928 14 6176 39603 31 _ _ (2117331 / 100000) (1058667 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568540928 :
    ThetaLowerSegment 1568540928 1568672000 (156849412752971 / 100000)
      (156862631306591 / 100000) := by
  exact
    packedTile65536 1568540928 1568672000 14 6243 39604 31 _ _ (105867 / 5000) (2117343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568672000 :
    ThetaLowerSegment 1568672000 1568803072 (156862631306591 / 100000)
      (156875693226403 / 100000) := by
  exact
    packedTile65536 1568672000 1568803072 14 6169 39606 31 _ _ (529337 / 25000) (2117351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568803072 :
    ThetaLowerSegment 1568803072 1568934144 (156875693226403 / 100000)
      (31377750192171 / 20000) := by
  exact
    packedTile65536 1568803072 1568934144 14 6167 39608 31 _ _ (529339 / 25000) (2117359 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1568934144 :
    ThetaLowerSegment 1568934144 1569065216 (31377750192171 / 20000) (31380378265609 / 20000) := by
  exact
    packedTile65536 1568934144 1569065216 14 6206 39609 31 _ _ (423473 / 20000) (264671 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569065216 :
    ThetaLowerSegment 1569065216 1569196288 (31380378265609 / 20000)
      (156914968223693 / 100000) := by
  exact
    packedTile65536 1569065216 1569196288 14 6176 39611 31 _ _ (2117373 / 100000) (66168 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569196288 :
    ThetaLowerSegment 1569196288 1569327360 (156914968223693 / 100000)
      (156928045168749 / 100000) := by
  exact
    packedTile65536 1569196288 1569327360 14 6176 39613 31 _ _ (2117381 / 100000) (264673 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569327360 :
    ThetaLowerSegment 1569327360 1569458432 (156928045168749 / 100000)
      (156941221686719 / 100000) := by
  exact
    packedTile65536 1569327360 1569458432 14 6223 39614 31 _ _ (211739 / 10000) (2117393 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569458432 :
    ThetaLowerSegment 1569458432 1569589504 (156941221686719 / 100000)
      (156954398254473 / 100000) := by
  exact
    packedTile65536 1569458432 1569589504 14 6223 39616 31 _ _ (1058699 / 50000) (2117401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569589504 :
    ThetaLowerSegment 1569589504 1569720576 (156954398254473 / 100000)
      (156967485940959 / 100000) := by
  exact
    packedTile65536 1569589504 1569720576 14 6181 39618 31 _ _ (1058703 / 50000) (2117409 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569720576 :
    ThetaLowerSegment 1569720576 1569851648 (156967485940959 / 100000)
      (156980512278039 / 100000) := by
  exact
    packedTile65536 1569720576 1569851648 14 6152 39619 31 _ _ (423483 / 20000) (1058709 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569851648 :
    ThetaLowerSegment 1569851648 1569982720 (156980512278039 / 100000)
      (39248449776841 / 25000) := by
  exact
    packedTile65536 1569851648 1569982720 14 6275 39621 31 _ _ (2117423 / 100000) (1058713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1569982720 :
    ThetaLowerSegment 1569982720 1570113792 (39248449776841 / 25000) (39251691565233 / 25000) := by
  exact
    packedTile65536 1569982720 1570113792 14 6124 39623 31 _ _ (264679 / 12500) (423487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1570113792 :
    ThetaLowerSegment 1570113792 1570244864 (39251691565233 / 25000) (39254987889953 / 25000) := by
  exact
    packedTile65536 1570113792 1570244864 14 6227 39624 31 _ _ (13234 / 625) (2117443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1570244864 :
    ThetaLowerSegment 1570244864 1570375936 (39254987889953 / 25000) (39258287403299 / 25000) := by
  exact
    packedTile65536 1570244864 1570375936 14 6233 39626 31 _ _ (264681 / 12500) (2117451 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1570375936 :
    ThetaLowerSegment 1570375936 1570507008 (39258287403299 / 25000) (39261539817251 / 25000) := by
  exact
    packedTile65536 1570375936 1570507008 14 6144 39627 31 _ _ (2117457 / 100000) (105873 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1570507008 :
    ThetaLowerSegment 1570507008 1570638080 (39261539817251 / 25000)
      (157059162621569 / 100000) := by
  exact
    packedTile65536 1570507008 1570638080 14 6141 39629 31 _ _ (423493 / 20000) (529367 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1570638080 :
    ThetaLowerSegment 1570638080 1570769152 (157059162621569 / 100000)
      (78536176180443 / 50000) := by
  exact
    packedTile65536 1570638080 1570769152 14 6229 39631 31 _ _ (2117473 / 100000) (529369 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1570769152 :
    ThetaLowerSegment 1570769152 1570900224 (78536176180443 / 50000) (9817840561691 / 6250) := by
  exact
    packedTile65536 1570769152 1570900224 14 6185 39632 31 _ _ (1058741 / 50000) (423497 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1570900224 :
    ThetaLowerSegment 1570900224 1571031296 (9817840561691 / 6250) (78549258008923 / 50000) := by
  exact
    packedTile65536 1570900224 1571031296 14 6171 39634 31 _ _ (211749 / 10000) (2117493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571031296 :
    ThetaLowerSegment 1571031296 1571162368 (78549258008923 / 50000) (39277889422007 / 25000) := by
  exact
    packedTile65536 1571031296 1571162368 14 6159 39636 31 _ _ (1058749 / 50000) (2117501 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571162368 :
    ThetaLowerSegment 1571162368 1571293440 (39277889422007 / 25000) (6284984992949 / 4000) := by
  exact
    packedTile65536 1571162368 1571293440 14 6171 39637 31 _ _ (2117507 / 100000) (211751 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571293440 :
    ThetaLowerSegment 1571293440 1571424512 (6284984992949 / 4000) (31427541366279 / 20000) := by
  exact
    packedTile65536 1571293440 1571424512 14 6178 39639 31 _ _ (423503 / 20000) (1058759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571424512 :
    ThetaLowerSegment 1571424512 1571555584 (31427541366279 / 20000) (15715084606161 / 10000) := by
  exact
    packedTile65536 1571424512 1571555584 14 6205 39641 31 _ _ (2117523 / 100000) (1058763 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571555584 :
    ThetaLowerSegment 1571555584 1571686656 (15715084606161 / 10000) (78581874092043 / 50000) := by
  exact
    packedTile65536 1571555584 1571686656 14 6093 39642 31 _ _ (529383 / 25000) (423507 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571686656 :
    ThetaLowerSegment 1571686656 1571817728 (78581874092043 / 50000) (78588351646903 / 50000) := by
  exact
    packedTile65536 1571686656 1571817728 14 6118 39644 31 _ _ (105877 / 5000) (2117543 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571817728 :
    ThetaLowerSegment 1571817728 1571948800 (78588351646903 / 50000) (78594973219499 / 50000) := by
  exact
    packedTile65536 1571817728 1571948800 14 6254 39646 31 _ _ (529387 / 25000) (2117551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1571948800 :
    ThetaLowerSegment 1571948800 1572079872 (78594973219499 / 50000) (78601546116427 / 50000) := by
  exact
    packedTile65536 1571948800 1572079872 14 6208 39647 31 _ _ (2117557 / 100000) (52939 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572079872 :
    ThetaLowerSegment 1572079872 1572210944 (78601546116427 / 50000)
      (157216261369589 / 100000) := by
  exact
    packedTile65536 1572079872 1572210944 14 6219 39649 31 _ _ (423513 / 20000) (66174 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572210944 :
    ThetaLowerSegment 1572210944 1572342016 (157216261369589 / 100000) (9826833586429 / 6250) := by
  exact
    packedTile65536 1572210944 1572342016 14 6175 39651 31 _ _ (2117573 / 100000) (264697 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572342016 :
    ThetaLowerSegment 1572342016 1572473088 (9826833586429 / 6250) (78621177079709 / 50000) := by
  exact
    packedTile65536 1572342016 1572473088 14 6147 39652 31 _ _ (1058791 / 50000) (423517 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572473088 :
    ThetaLowerSegment 1572473088 1572604160 (78621177079709 / 50000) (19656940960851 / 12500) := by
  exact
    packedTile65536 1572473088 1572604160 14 6221 39654 31 _ _ (211759 / 10000) (2117593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572604160 :
    ThetaLowerSegment 1572604160 1572735232 (19656940960851 / 12500) (4914643671927 / 3125) := by
  exact
    packedTile65536 1572604160 1572735232 14 6172 39656 31 _ _ (1058799 / 50000) (2117601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572735232 :
    ThetaLowerSegment 1572735232 1572866304 (4914643671927 / 3125) (157281525492399 / 100000) := by
  exact
    packedTile65536 1572735232 1572866304 14 6105 39657 31 _ _ (2117607 / 100000) (211761 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572866304 :
    ThetaLowerSegment 1572866304 1572997376 (157281525492399 / 100000)
      (78647370763807 / 50000) := by
  exact
    packedTile65536 1572866304 1572997376 14 6241 39659 31 _ _ (423523 / 20000) (1058809 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1572997376 :
    ThetaLowerSegment 1572997376 1573128448 (78647370763807 / 50000) (39326964521119 / 25000) := by
  exact
    packedTile65536 1572997376 1573128448 14 6194 39661 31 _ _ (2117623 / 100000) (1058813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573128448 :
    ThetaLowerSegment 1573128448 1573259520 (39326964521119 / 25000) (39330214556831 / 25000) := by
  exact
    packedTile65536 1573128448 1573259520 14 6139 39662 31 _ _ (66176 / 3125) (423527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573259520 :
    ThetaLowerSegment 1573259520 1573390592 (39330214556831 / 25000) (39333536075171 / 25000) := by
  exact
    packedTile65536 1573259520 1573390592 14 6274 39664 31 _ _ (52941 / 2500) (2117643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573390592 :
    ThetaLowerSegment 1573390592 1573521664 (39333536075171 / 25000) (39336790900147 / 25000) := by
  exact
    packedTile65536 1573390592 1573521664 14 6148 39665 31 _ _ (132353 / 6250) (2117651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573521664 :
    ThetaLowerSegment 1573521664 1573652736 (39336790900147 / 25000)
      (157360261309133 / 100000) := by
  exact
    packedTile65536 1573521664 1573652736 14 6185 39667 31 _ _ (2117657 / 100000) (105883 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573652736 :
    ThetaLowerSegment 1573652736 1573783808 (157360261309133 / 100000) (9835829912243 / 6250) := by
  exact
    packedTile65536 1573652736 1573783808 14 6147 39669 31 _ _ (423533 / 20000) (529417 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573783808 :
    ThetaLowerSegment 1573783808 1573914880 (9835829912243 / 6250) (157386372168047 / 100000) := by
  exact
    packedTile65536 1573783808 1573914880 14 6183 39670 31 _ _ (2117673 / 100000) (529419 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1573914880 :
    ThetaLowerSegment 1573914880 1574045952 (157386372168047 / 100000)
      (157399315440431 / 100000) := by
  exact
    packedTile65536 1573914880 1574045952 14 6112 39672 31 _ _ (1058841 / 50000) (423537 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574045952 :
    ThetaLowerSegment 1574045952 1574177024 (157399315440431 / 100000)
      (157412487472231 / 100000) := by
  exact
    packedTile65536 1574045952 1574177024 14 6220 39674 31 _ _ (211769 / 10000) (2117693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574177024 :
    ThetaLowerSegment 1574177024 1574308096 (157412487472231 / 100000)
      (31485139534471 / 20000) := by
  exact
    packedTile65536 1574177024 1574308096 14 6238 39675 31 _ _ (1058849 / 50000) (2117701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574308096 :
    ThetaLowerSegment 1574308096 1574439168 (31485139534471 / 20000) (78719372432591 / 50000) := by
  exact
    packedTile65536 1574308096 1574439168 14 6161 39677 31 _ _ (2117707 / 100000) (211771 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574439168 :
    ThetaLowerSegment 1574439168 1574570240 (78719372432591 / 50000) (78725958526241 / 50000) := by
  exact
    packedTile65536 1574439168 1574570240 14 6220 39679 31 _ _ (423543 / 20000) (1058859 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574570240 :
    ThetaLowerSegment 1574570240 1574701312 (78725958526241 / 50000)
      (157465032111021 / 100000) := by
  exact
    packedTile65536 1574570240 1574701312 14 6193 39680 31 _ _ (2117723 / 100000) (1058863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574701312 :
    ThetaLowerSegment 1574701312 1574832384 (157465032111021 / 100000)
      (157478244640969 / 100000) := by
  exact
    packedTile65536 1574701312 1574832384 14 6239 39682 31 _ _ (529433 / 25000) (423547 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574832384 :
    ThetaLowerSegment 1574832384 1574963456 (157478244640969 / 100000)
      (157491488986929 / 100000) := by
  exact
    packedTile65536 1574832384 1574963456 14 6254 39684 31 _ _ (105887 / 5000) (2117743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1574963456 :
    ThetaLowerSegment 1574963456 1575094528 (157491488986929 / 100000)
      (157504631731017 / 100000) := by
  exact
    packedTile65536 1574963456 1575094528 14 6206 39685 31 _ _ (529437 / 25000) (2117751 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1575094528 :
    ThetaLowerSegment 1575094528 1575225600 (157504631731017 / 100000)
      (78758856558003 / 50000) := by
  exact
    packedTile65536 1575094528 1575225600 14 6177 39687 31 _ _ (2117757 / 100000) (13236 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1575225600 :
    ThetaLowerSegment 1575225600 1575356672 (78758856558003 / 50000) (4922836336998 / 3125) := by
  exact
    packedTile65536 1575225600 1575356672 14 6162 39689 31 _ _ (423553 / 20000) (264721 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1575356672 :
    ThetaLowerSegment 1575356672 1575487744 (4922836336998 / 3125) (39385992304091 / 25000) := by
  exact
    packedTile65536 1575356672 1575487744 14 6236 39690 31 _ _ (2117773 / 100000) (132361 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1575487744 :
    ThetaLowerSegment 1575487744 1575618816 (39385992304091 / 25000) (3938926321839 / 2500) := by
  exact
    packedTile65536 1575487744 1575618816 14 6178 39692 31 _ _ (1058891 / 50000) (423557 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1575618816 :
    ThetaLowerSegment 1575618816 1575749888 (3938926321839 / 2500) (1969628454429 / 1250) := by
  exact
    packedTile65536 1575618816 1575749888 14 6244 39694 31 _ _ (211779 / 10000) (2117793 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1575749888 :
    ThetaLowerSegment 1575749888 1575880960 (1969628454429 / 1250) (78791642993717 / 50000) := by
  exact
    packedTile65536 1575749888 1575880960 14 6143 39695 31 _ _ (1058899 / 50000) (2117801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1575880960 :
    ThetaLowerSegment 1575880960 1576012032 (78791642993717 / 50000)
      (157596291440221 / 100000) := by
  exact
    packedTile65536 1575880960 1576012032 14 6141 39697 31 _ _ (2117807 / 100000) (211781 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576012032 :
    ThetaLowerSegment 1576012032 1576143104 (157596291440221 / 100000)
      (78804616703843 / 50000) := by
  exact
    packedTile65536 1576012032 1576143104 14 6111 39699 31 _ _ (423563 / 20000) (1058909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576143104 :
    ThetaLowerSegment 1576143104 1576274176 (78804616703843 / 50000) (3940561109689 / 2500) := by
  exact
    packedTile65536 1576143104 1576274176 14 6238 39700 31 _ _ (2117823 / 100000) (1058913 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576274176 :
    ThetaLowerSegment 1576274176 1576405248 (3940561109689 / 2500) (39408874674461 / 25000) := by
  exact
    packedTile65536 1576274176 1576405248 14 6164 39702 31 _ _ (2117831 / 100000) (1058917 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576405248 :
    ThetaLowerSegment 1576405248 1576536320 (39408874674461 / 25000) (39412221920581 / 25000) := by
  exact
    packedTile65536 1576405248 1576536320 14 6322 39703 31 _ _ (26473 / 1250) (2117843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576536320 :
    ThetaLowerSegment 1576536320 1576667392 (39412221920581 / 25000) (7883103776091 / 5000) := by
  exact
    packedTile65536 1576536320 1576667392 14 6227 39705 31 _ _ (264731 / 12500) (2117851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576667392 :
    ThetaLowerSegment 1576667392 1576798464 (7883103776091 / 5000) (39418832266167 / 25000) := by
  exact
    packedTile65536 1576667392 1576798464 14 6258 39707 31 _ _ (66183 / 3125) (2117859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576798464 :
    ThetaLowerSegment 1576798464 1576929536 (39418832266167 / 25000)
      (157688309459253 / 100000) := by
  exact
    packedTile65536 1576798464 1576929536 14 6129 39708 31 _ _ (423573 / 20000) (529467 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1576929536 :
    ThetaLowerSegment 1576929536 1577060608 (157688309459253 / 100000)
      (39425384952971 / 25000) := by
  exact
    packedTile65536 1576929536 1577060608 14 6247 39710 31 _ _ (2117873 / 100000) (529469 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577060608 :
    ThetaLowerSegment 1577060608 1577191680 (39425384952971 / 25000) (19714305242867 / 12500) := by
  exact
    packedTile65536 1577060608 1577191680 14 6092 39712 31 _ _ (2117881 / 100000) (529471 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577191680 :
    ThetaLowerSegment 1577191680 1577322752 (19714305242867 / 12500) (39431851916379 / 25000) := by
  exact
    packedTile65536 1577191680 1577322752 14 6122 39713 31 _ _ (211789 / 10000) (2117893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577322752 :
    ThetaLowerSegment 1577322752 1577339136 (39431851916379 / 25000) (78864467334987 / 50000) := by
  exact
    packedTile65536 1577322752 1577339136 11 721 39715 31 _ _ (1058949 / 50000) (2117901 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell1577339136 :
    ThetaLowerSegment 1577339136 1577341184 (78864467334987 / 50000)
      (157729148577773 / 100000) := by
  exact
    packedTile65536 1577339136 1577341184 8 101 39715 31 _ _ (2117899 / 100000) (1058951 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_1545341184_1577341184 :
    ThetaLowerSegment 1545341184 1577341184 (77265055344773 / 50000)
      (157729148577773 / 100000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1545341184 cell1545472256)
                  (ThetaLowerSegment.join cell1545603328 cell1545734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1545865472 cell1545996544)
                  (ThetaLowerSegment.join cell1546127616 cell1546258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1546389760 cell1546520832)
                  (ThetaLowerSegment.join cell1546651904 cell1546782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1546914048 cell1547045120)
                  (ThetaLowerSegment.join cell1547176192 cell1547307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1547438336 cell1547569408)
                  (ThetaLowerSegment.join cell1547700480 cell1547831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1547962624 cell1548093696)
                  (ThetaLowerSegment.join cell1548224768 cell1548355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1548486912 cell1548617984)
                  (ThetaLowerSegment.join cell1548749056 cell1548880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1549011200 cell1549142272)
                  (ThetaLowerSegment.join cell1549273344 cell1549404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1549535488 cell1549666560)
                  (ThetaLowerSegment.join cell1549797632 cell1549928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1550059776 cell1550190848)
                  (ThetaLowerSegment.join cell1550321920 cell1550452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1550584064 cell1550715136)
                  (ThetaLowerSegment.join cell1550846208 cell1550977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1551108352 cell1551239424)
                  (ThetaLowerSegment.join cell1551370496 cell1551501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1551632640 cell1551763712)
                  (ThetaLowerSegment.join cell1551894784 cell1552025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1552156928 cell1552288000)
                  (ThetaLowerSegment.join cell1552419072 cell1552550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1552681216 cell1552812288)
                  (ThetaLowerSegment.join cell1552943360 cell1553074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1553205504 cell1553336576)
                  (ThetaLowerSegment.join cell1553467648 cell1553598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1553729792 cell1553860864)
                  (ThetaLowerSegment.join cell1553991936 cell1554123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1554254080 cell1554385152)
                  (ThetaLowerSegment.join cell1554516224 cell1554647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1554778368 cell1554909440)
                  (ThetaLowerSegment.join cell1555040512 cell1555171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1555302656 cell1555433728)
                  (ThetaLowerSegment.join cell1555564800 cell1555695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1555826944 cell1555958016)
                  (ThetaLowerSegment.join cell1556089088 cell1556220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1556351232 cell1556482304)
                  (ThetaLowerSegment.join cell1556613376 cell1556744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1556875520 cell1557006592)
                  (ThetaLowerSegment.join cell1557137664 cell1557268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1557399808 cell1557530880)
                  (ThetaLowerSegment.join cell1557661952 cell1557793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1557924096 cell1558055168)
                  (ThetaLowerSegment.join cell1558186240 cell1558317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1558448384 cell1558579456)
                  (ThetaLowerSegment.join cell1558710528 cell1558841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1558972672 cell1559103744)
                  (ThetaLowerSegment.join cell1559234816 cell1559365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1559496960 cell1559628032)
                  (ThetaLowerSegment.join cell1559759104 cell1559890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1560021248 cell1560152320)
                  (ThetaLowerSegment.join cell1560283392 cell1560414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1560545536 cell1560676608)
                  (ThetaLowerSegment.join cell1560807680 cell1560938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1561069824 cell1561200896)
                  (ThetaLowerSegment.join cell1561331968 cell1561463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1561594112 cell1561725184)
                  (ThetaLowerSegment.join cell1561856256 cell1561987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1562118400 cell1562249472)
                  (ThetaLowerSegment.join cell1562380544 cell1562511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1562642688 cell1562773760)
                  (ThetaLowerSegment.join cell1562904832 cell1563035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1563166976 cell1563298048)
                  (ThetaLowerSegment.join cell1563429120 cell1563560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1563691264 cell1563822336)
                  (ThetaLowerSegment.join cell1563953408 cell1564084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1564215552 cell1564346624)
                  (ThetaLowerSegment.join cell1564477696 cell1564608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1564739840 cell1564870912)
                  (ThetaLowerSegment.join cell1565001984 cell1565133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1565264128 cell1565395200)
                  (ThetaLowerSegment.join cell1565526272 cell1565657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1565788416 cell1565919488)
                  (ThetaLowerSegment.join cell1566050560 cell1566181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1566312704 cell1566443776)
                  (ThetaLowerSegment.join cell1566574848 cell1566705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1566836992 cell1566968064)
                  (ThetaLowerSegment.join cell1567099136 cell1567230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1567361280 cell1567492352)
                  (ThetaLowerSegment.join cell1567623424 cell1567754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1567885568 cell1568016640)
                  (ThetaLowerSegment.join cell1568147712 cell1568278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1568409856 cell1568540928)
                  (ThetaLowerSegment.join cell1568672000 cell1568803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1568934144 cell1569065216)
                  (ThetaLowerSegment.join cell1569196288 cell1569327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1569458432 cell1569589504)
                  (ThetaLowerSegment.join cell1569720576 cell1569851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1569982720 cell1570113792)
                  (ThetaLowerSegment.join cell1570244864 cell1570375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1570507008 cell1570638080)
                  (ThetaLowerSegment.join cell1570769152 cell1570900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1571031296 cell1571162368)
                  (ThetaLowerSegment.join cell1571293440 cell1571424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1571555584 cell1571686656)
                  (ThetaLowerSegment.join cell1571817728 cell1571948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1572079872 cell1572210944)
                  (ThetaLowerSegment.join cell1572342016 cell1572473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1572604160 cell1572735232)
                  (ThetaLowerSegment.join cell1572866304 cell1572997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1573128448 cell1573259520)
                  (ThetaLowerSegment.join cell1573390592 cell1573521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1573652736 cell1573783808)
                  (ThetaLowerSegment.join cell1573914880 cell1574045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1574177024 cell1574308096)
                  (ThetaLowerSegment.join cell1574439168 cell1574570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1574701312 cell1574832384)
                  (ThetaLowerSegment.join cell1574963456 cell1575094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1575225600 cell1575356672)
                  (ThetaLowerSegment.join cell1575487744 cell1575618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1575749888 cell1575880960)
                  (ThetaLowerSegment.join cell1576012032 cell1576143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell1576274176 cell1576405248)
                  (ThetaLowerSegment.join cell1576536320 cell1576667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell1576798464 cell1576929536)
                (ThetaLowerSegment.join cell1577060608 cell1577191680))
              (ThetaLowerSegment.join cell1577322752 cell1577339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
