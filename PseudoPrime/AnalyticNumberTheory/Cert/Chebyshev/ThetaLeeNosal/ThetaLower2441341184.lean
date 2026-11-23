/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2441341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2409341184 :
    ThetaLowerSegment 2409341184 2409472256 (120463607486549 / 50000)
      (120470200600069 / 50000) := by
  exact
    packedTile65536 2409341184 2409472256 14 6104 49085 31 _ _ (108013 / 5000) (2160263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409472256 :
    ThetaLowerSegment 2409472256 2409603328 (120470200600069 / 50000) (60238365002027 / 25000) := by
  exact
    packedTile65536 2409472256 2409603328 14 6045 49086 31 _ _ (1080133 / 50000) (2160269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409603328 :
    ThetaLowerSegment 2409603328 2409734400 (60238365002027 / 25000)
      (240966700309067 / 100000) := by
  exact
    packedTile65536 2409603328 2409734400 14 6129 49087 31 _ _ (2160271 / 100000) (1080137 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409734400 :
    ThetaLowerSegment 2409734400 2409865472 (240966700309067 / 100000)
      (48195942763543 / 20000) := by
  exact
    packedTile65536 2409734400 2409865472 14 6024 49089 31 _ _ (2160277 / 100000) (54007 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409865472 :
    ThetaLowerSegment 2409865472 2409996544 (48195942763543 / 20000)
      (240992820248609 / 100000) := by
  exact
    packedTile65536 2409865472 2409996544 14 6067 49090 31 _ _ (1080141 / 50000) (432057 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2409996544 :
    ThetaLowerSegment 2409996544 2410127616 (240992820248609 / 100000) (9640238364809 / 4000) := by
  exact
    packedTile65536 2409996544 2410127616 14 6082 49091 31 _ _ (67509 / 3125) (2160291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2410127616 :
    ThetaLowerSegment 2410127616 2410258688 (9640238364809 / 4000) (48203797137403 / 20000) := by
  exact
    packedTile65536 2410127616 2410258688 14 6030 49093 31 _ _ (2160293 / 100000) (270037 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2410258688 :
    ThetaLowerSegment 2410258688 2410389760 (48203797137403 / 20000)
      (241032124619451 / 100000) := by
  exact
    packedTile65536 2410258688 2410389760 14 6082 49094 31 _ _ (1080149 / 50000) (2160301 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2410389760 :
    ThetaLowerSegment 2410389760 2410520832 (241032124619451 / 100000)
      (48209026361967 / 20000) := by
  exact
    packedTile65536 2410389760 2410520832 14 6021 49095 31 _ _ (135019 / 6250) (2160307 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2410520832 :
    ThetaLowerSegment 2410520832 2410651904 (48209026361967 / 20000)
      (241058188717431 / 100000) := by
  exact
    packedTile65536 2410520832 2410651904 14 6044 49097 31 _ _ (2160309 / 100000) (270039 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2410651904 :
    ThetaLowerSegment 2410651904 2410782976 (241058188717431 / 100000)
      (241071440089641 / 100000) := by
  exact
    packedTile65536 2410651904 2410782976 14 6134 49098 31 _ _ (432063 / 20000) (1080159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2410782976 :
    ThetaLowerSegment 2410782976 2410914048 (241071440089641 / 100000)
      (241084425773161 / 100000) := by
  exact
    packedTile65536 2410782976 2410914048 14 6011 49099 31 _ _ (13502 / 625) (2160323 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2410914048 :
    ThetaLowerSegment 2410914048 2411045120 (241084425773161 / 100000)
      (241097586479153 / 100000) := by
  exact
    packedTile65536 2410914048 2411045120 14 6092 49101 31 _ _ (1080163 / 50000) (2160329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411045120 :
    ThetaLowerSegment 2411045120 2411176192 (241097586479153 / 100000)
      (48222119198487 / 20000) := by
  exact
    packedTile65536 2411045120 2411176192 14 6022 49102 31 _ _ (2160331 / 100000) (1080167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411176192 :
    ThetaLowerSegment 2411176192 2411307264 (48222119198487 / 20000) (120561929150639 / 50000) := by
  exact
    packedTile65536 2411176192 2411307264 14 6139 49103 31 _ _ (2160337 / 100000) (108017 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411307264 :
    ThetaLowerSegment 2411307264 2411438336 (120561929150639 / 50000)
      (120568477147241 / 50000) := by
  exact
    packedTile65536 2411307264 2411438336 14 6062 49105 31 _ _ (1080171 / 50000) (432069 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411438336 :
    ThetaLowerSegment 2411438336 2411569408 (120568477147241 / 50000)
      (120575010036569 / 50000) := by
  exact
    packedTile65536 2411438336 2411569408 14 6048 49106 31 _ _ (2160347 / 100000) (43207 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411569408 :
    ThetaLowerSegment 2411569408 2411700480 (120575010036569 / 50000) (60290820079963 / 25000) := by
  exact
    packedTile65536 2411569408 2411700480 14 6138 49107 31 _ _ (2160353 / 100000) (540089 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411700480 :
    ThetaLowerSegment 2411700480 2411831552 (60290820079963 / 25000) (3014705353233 / 1250) := by
  exact
    packedTile65536 2411700480 2411831552 14 6086 49109 31 _ _ (1080179 / 50000) (2160361 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411831552 :
    ThetaLowerSegment 2411831552 2411962624 (3014705353233 / 1250) (30148672185057 / 12500) := by
  exact
    packedTile65536 2411831552 2411962624 14 5994 49110 31 _ _ (540091 / 25000) (2160367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2411962624 :
    ThetaLowerSegment 2411962624 2412093696 (30148672185057 / 12500) (120601232497929 / 50000) := by
  exact
    packedTile65536 2411962624 2412093696 14 6058 49111 31 _ _ (2160369 / 100000) (540093 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2412093696 :
    ThetaLowerSegment 2412093696 2412224768 (120601232497929 / 50000) (60303868693527 / 25000) := by
  exact
    packedTile65536 2412093696 2412224768 14 6022 49113 31 _ _ (17283 / 800) (1080189 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2412224768 :
    ThetaLowerSegment 2412224768 2412355840 (60303868693527 / 25000) (30153579746181 / 12500) := by
  exact
    packedTile65536 2412224768 2412355840 14 6093 49114 31 _ _ (108019 / 5000) (2160383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2412355840 :
    ThetaLowerSegment 2412355840 2412486912 (30153579746181 / 12500) (60310423834097 / 25000) := by
  exact
    packedTile65536 2412355840 2412486912 14 6044 49115 31 _ _ (432077 / 20000) (540097 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2412486912 :
    ThetaLowerSegment 2412486912 2412617984 (60310423834097 / 25000) (15078429607593 / 6250) := by
  exact
    packedTile65536 2412486912 2412617984 14 6100 49117 31 _ _ (2160391 / 100000) (1080197 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2412617984 :
    ThetaLowerSegment 2412617984 2412749056 (15078429607593 / 6250) (7539624468888 / 3125) := by
  exact
    packedTile65536 2412617984 2412749056 14 6068 49118 31 _ _ (540099 / 25000) (2160399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2412749056 :
    ThetaLowerSegment 2412749056 2412880128 (7539624468888 / 3125) (12064058288871 / 5000) := by
  exact
    packedTile65536 2412749056 2412880128 14 6102 49119 31 _ _ (1080201 / 50000) (432081 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2412880128 :
    ThetaLowerSegment 2412880128 2413011200 (12064058288871 / 5000) (120647178611281 / 50000) := by
  exact
    packedTile65536 2412880128 2413011200 14 6106 49121 31 _ _ (2160407 / 100000) (216041 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413011200 :
    ThetaLowerSegment 2413011200 2413142272 (120647178611281 / 50000)
      (120653668491933 / 50000) := by
  exact
    packedTile65536 2413011200 2413142272 14 6008 49122 31 _ _ (2160413 / 100000) (67513 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413142272 :
    ThetaLowerSegment 2413142272 2413273344 (120653668491933 / 50000) (60330105658923 / 25000) := by
  exact
    packedTile65536 2413142272 2413273344 14 6057 49123 31 _ _ (1080209 / 50000) (2160421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413273344 :
    ThetaLowerSegment 2413273344 2413404416 (60330105658923 / 25000) (48266737958667 / 20000) := by
  exact
    packedTile65536 2413273344 2413404416 14 6141 49125 31 _ _ (2160423 / 100000) (1080213 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413404416 :
    ThetaLowerSegment 2413404416 2413535488 (48266737958667 / 20000) (24134677119093 / 10000) := by
  exact
    packedTile65536 2413404416 2413535488 14 6055 49126 31 _ _ (2160429 / 100000) (135027 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413535488 :
    ThetaLowerSegment 2413535488 2413666560 (24134677119093 / 10000) (120679806405313 / 50000) := by
  exact
    packedTile65536 2413535488 2413666560 14 5944 49127 31 _ _ (1080217 / 50000) (2160437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413666560 :
    ThetaLowerSegment 2413666560 2413797632 (120679806405313 / 50000)
      (120686360100053 / 50000) := by
  exact
    packedTile65536 2413666560 2413797632 14 6067 49129 31 _ _ (54011 / 2500) (2160443 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413797632 :
    ThetaLowerSegment 2413797632 2413928704 (120686360100053 / 50000)
      (241385827619921 / 100000) := by
  exact
    packedTile65536 2413797632 2413928704 14 6067 49130 31 _ _ (432089 / 20000) (67514 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2413928704 :
    ThetaLowerSegment 2413928704 2414059776 (241385827619921 / 100000)
      (48279815965271 / 20000) := by
  exact
    packedTile65536 2413928704 2414059776 14 6134 49131 31 _ _ (2160451 / 100000) (1080227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414059776 :
    ThetaLowerSegment 2414059776 2414190848 (48279815965271 / 20000) (1931297118263 / 800) := by
  exact
    packedTile65536 2414059776 2414190848 14 6045 49133 31 _ _ (270057 / 12500) (2160459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414190848 :
    ThetaLowerSegment 2414190848 2414321920 (1931297118263 / 800) (241425258108139 / 100000) := by
  exact
    packedTile65536 2414190848 2414321920 14 6072 49134 31 _ _ (1080231 / 50000) (432093 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414321920 :
    ThetaLowerSegment 2414321920 2414452992 (241425258108139 / 100000)
      (120719215237719 / 50000) := by
  exact
    packedTile65536 2414321920 2414452992 14 6097 49135 31 _ _ (2160467 / 100000) (216047 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414452992 :
    ThetaLowerSegment 2414452992 2414584064 (120719215237719 / 50000)
      (120725731221271 / 50000) := by
  exact
    packedTile65536 2414452992 2414584064 14 6032 49137 31 _ _ (270059 / 12500) (86419 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414584064 :
    ThetaLowerSegment 2414584064 2414715136 (120725731221271 / 50000)
      (120732292592957 / 50000) := by
  exact
    packedTile65536 2414584064 2414715136 14 6074 49138 31 _ _ (1080239 / 50000) (2160481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414715136 :
    ThetaLowerSegment 2414715136 2414846208 (120732292592957 / 50000) (60369433471363 / 25000) := by
  exact
    packedTile65536 2414715136 2414846208 14 6086 49139 31 _ _ (2160483 / 100000) (1080243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414846208 :
    ThetaLowerSegment 2414846208 2414977280 (60369433471363 / 25000)
      (241490750831677 / 100000) := by
  exact
    packedTile65536 2414846208 2414977280 14 6025 49141 31 _ _ (2160489 / 100000) (540123 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2414977280 :
    ThetaLowerSegment 2414977280 2415108352 (241490750831677 / 100000)
      (48300795475189 / 20000) := by
  exact
    packedTile65536 2414977280 2415108352 14 6122 49142 31 _ _ (1080247 / 50000) (2160497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2415108352 :
    ThetaLowerSegment 2415108352 2415239424 (48300795475189 / 20000)
      (241516957653937 / 100000) := by
  exact
    packedTile65536 2415108352 2415239424 14 6008 49143 31 _ _ (2160499 / 100000) (1080251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2415239424 :
    ThetaLowerSegment 2415239424 2415370496 (241516957653937 / 100000)
      (241529937967977 / 100000) := by
  exact
    packedTile65536 2415239424 2415370496 14 6008 49145 31 _ _ (432101 / 20000) (540127 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2415370496 :
    ThetaLowerSegment 2415370496 2415501568 (241529937967977 / 100000)
      (241543000411437 / 100000) := by
  exact
    packedTile65536 2415370496 2415501568 14 6046 49146 31 _ _ (216051 / 10000) (2160513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2415501568 :
    ThetaLowerSegment 2415501568 2415632640 (241543000411437 / 100000)
      (48311204800377 / 20000) := by
  exact
    packedTile65536 2415501568 2415632640 14 6028 49147 31 _ _ (540129 / 25000) (2160519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2415632640 :
    ThetaLowerSegment 2415632640 2415763712 (48311204800377 / 20000) (12078455297827 / 5000) := by
  exact
    packedTile65536 2415632640 2415763712 14 6055 49149 31 _ _ (2160521 / 100000) (540131 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2415763712 :
    ThetaLowerSegment 2415763712 2415894784 (12078455297827 / 5000) (120791123140877 / 50000) := by
  exact
    packedTile65536 2415763712 2415894784 14 6082 49150 31 _ _ (2160527 / 100000) (216053 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2415894784 :
    ThetaLowerSegment 2415894784 2416025856 (120791123140877 / 50000)
      (120797637144857 / 50000) := by
  exact
    packedTile65536 2415894784 2416025856 14 6030 49151 31 _ _ (540133 / 25000) (432107 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416025856 :
    ThetaLowerSegment 2416025856 2416156928 (120797637144857 / 50000)
      (241608213745807 / 100000) := by
  exact
    packedTile65536 2416025856 2416156928 14 5989 49153 31 _ _ (2160537 / 100000) (108027 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416156928 :
    ThetaLowerSegment 2416156928 2416288000 (241608213745807 / 100000)
      (60405356366563 / 25000) := by
  exact
    packedTile65536 2416156928 2416288000 14 6115 49154 31 _ _ (2160543 / 100000) (1080273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416288000 :
    ThetaLowerSegment 2416288000 2416419072 (60405356366563 / 25000) (2416345529559 / 1000) := by
  exact
    packedTile65536 2416288000 2416419072 14 6076 49155 31 _ _ (540137 / 25000) (2160551 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416419072 :
    ThetaLowerSegment 2416419072 2416550144 (2416345529559 / 1000) (24164761350483 / 10000) := by
  exact
    packedTile65536 2416419072 2416550144 14 6045 49157 31 _ _ (1080277 / 50000) (2160557 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416550144 :
    ThetaLowerSegment 2416550144 2416681216 (24164761350483 / 10000)
      (241660622230569 / 100000) := by
  exact
    packedTile65536 2416550144 2416681216 14 6021 49158 31 _ _ (2160559 / 100000) (1080281 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416681216 :
    ThetaLowerSegment 2416681216 2416812288 (241660622230569 / 100000)
      (60418452039691 / 25000) := by
  exact
    packedTile65536 2416681216 2416812288 14 6103 49159 31 _ _ (432113 / 20000) (270071 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416812288 :
    ThetaLowerSegment 2416812288 2416943360 (60418452039691 / 25000) (60421742587801 / 25000) := by
  exact
    packedTile65536 2416812288 2416943360 14 6092 49161 31 _ _ (216057 / 10000) (2160573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2416943360 :
    ThetaLowerSegment 2416943360 2417074432 (60421742587801 / 25000) (60425052588701 / 25000) := by
  exact
    packedTile65536 2416943360 2417074432 14 6128 49162 31 _ _ (86423 / 4000) (1080289 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417074432 :
    ThetaLowerSegment 2417074432 2417205504 (60425052588701 / 25000) (3021414564981 / 1250) := by
  exact
    packedTile65536 2417074432 2417205504 14 5996 49163 31 _ _ (2160581 / 100000) (270073 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417205504 :
    ThetaLowerSegment 2417205504 2417336576 (3021414564981 / 1250) (120863192912107 / 50000) := by
  exact
    packedTile65536 2417205504 2417336576 14 6119 49165 31 _ _ (1080293 / 50000) (2160589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417336576 :
    ThetaLowerSegment 2417336576 2417467648 (120863192912107 / 50000)
      (120869745987643 / 50000) := by
  exact
    packedTile65536 2417336576 2417467648 14 6066 49166 31 _ _ (135037 / 6250) (432119 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417467648 :
    ThetaLowerSegment 2417467648 2417598720 (120869745987643 / 50000)
      (241752626244449 / 100000) := by
  exact
    packedTile65536 2417467648 2417598720 14 6079 49167 31 _ _ (2160597 / 100000) (10803 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417598720 :
    ThetaLowerSegment 2417598720 2417729792 (241752626244449 / 100000) (15110364085511 / 6250) := by
  exact
    packedTile65536 2417598720 2417729792 14 6109 49169 31 _ _ (2160603 / 100000) (1080303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417729792 :
    ThetaLowerSegment 2417729792 2417860864 (15110364085511 / 6250) (15111173098169 / 6250) := by
  exact
    packedTile65536 2417729792 2417860864 14 5991 49170 31 _ _ (67519 / 3125) (2160611 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417860864 :
    ThetaLowerSegment 2417860864 2417991936 (15111173098169 / 6250) (48358379923181 / 20000) := by
  exact
    packedTile65536 2417860864 2417991936 14 6077 49171 31 _ _ (2160613 / 100000) (270077 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2417991936 :
    ThetaLowerSegment 2417991936 2418123008 (48358379923181 / 20000) (120902456512071 / 50000) := by
  exact
    packedTile65536 2417991936 2418123008 14 6023 49173 31 _ _ (2160619 / 100000) (1080311 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2418123008 :
    ThetaLowerSegment 2418123008 2418254080 (120902456512071 / 50000)
      (120909012925599 / 50000) := by
  exact
    packedTile65536 2418123008 2418254080 14 6069 49174 31 _ _ (135039 / 6250) (2160627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2418254080 :
    ThetaLowerSegment 2418254080 2418385152 (120909012925599 / 50000)
      (120915550991979 / 50000) := by
  exact
    packedTile65536 2418254080 2418385152 14 6052 49175 31 _ _ (216063 / 10000) (2160633 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2418385152 :
    ThetaLowerSegment 2418385152 2418516224 (120915550991979 / 50000)
      (120922223032859 / 50000) := by
  exact
    packedTile65536 2418385152 2418516224 14 6176 49177 31 _ _ (432127 / 20000) (1080319 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2418516224 :
    ThetaLowerSegment 2418516224 2418647296 (120922223032859 / 50000)
      (120928843236883 / 50000) := by
  exact
    packedTile65536 2418516224 2418647296 14 6128 49178 31 _ _ (2160641 / 100000) (540161 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2418647296 :
    ThetaLowerSegment 2418647296 2418778368 (120928843236883 / 50000) (24187100469571 / 10000) := by
  exact
    packedTile65536 2418647296 2418778368 14 6164 49179 31 _ _ (1080323 / 50000) (2160649 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2418778368 :
    ThetaLowerSegment 2418778368 2418909440 (24187100469571 / 10000)
      (241884061509703 / 100000) := by
  exact
    packedTile65536 2418778368 2418909440 14 6043 49181 31 _ _ (2160651 / 100000) (1080327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2418909440 :
    ThetaLowerSegment 2418909440 2419040512 (241884061509703 / 100000)
      (120948658570199 / 50000) := by
  exact
    packedTile65536 2418909440 2419040512 14 6135 49182 31 _ _ (2160657 / 100000) (108033 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419040512 :
    ThetaLowerSegment 2419040512 2419171584 (120948658570199 / 50000) (15119390813987 / 6250) := by
  exact
    packedTile65536 2419040512 2419171584 14 5987 49183 31 _ _ (1080331 / 50000) (432133 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419171584 :
    ThetaLowerSegment 2419171584 2419302656 (15119390813987 / 6250) (12096172843297 / 5000) := by
  exact
    packedTile65536 2419171584 2419302656 14 6111 49185 31 _ _ (540167 / 25000) (2160671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419302656 :
    ThetaLowerSegment 2419302656 2419433728 (12096172843297 / 5000) (48387307948191 / 20000) := by
  exact
    packedTile65536 2419302656 2419433728 14 6055 49186 31 _ _ (2160673 / 100000) (540169 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419433728 :
    ThetaLowerSegment 2419433728 2419564800 (48387307948191 / 20000)
      (241949791179129 / 100000) := by
  exact
    packedTile65536 2419433728 2419564800 14 6133 49187 31 _ _ (1080339 / 50000) (2160681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419564800 :
    ThetaLowerSegment 2419564800 2419695872 (241949791179129 / 100000)
      (241962852513909 / 100000) := by
  exact
    packedTile65536 2419564800 2419695872 14 6045 49189 31 _ _ (540171 / 25000) (2160687 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419695872 :
    ThetaLowerSegment 2419695872 2419826944 (241962852513909 / 100000)
      (120987969903591 / 50000) := by
  exact
    packedTile65536 2419695872 2419826944 14 6057 49190 31 _ _ (2160689 / 100000) (540173 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419826944 :
    ThetaLowerSegment 2419826944 2419958016 (120987969903591 / 50000) (15124310549877 / 6250) := by
  exact
    packedTile65536 2419826944 2419958016 14 6030 49191 31 _ _ (432139 / 20000) (1080349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2419958016 :
    ThetaLowerSegment 2419958016 2420089088 (15124310549877 / 6250) (30250244325629 / 12500) := by
  exact
    packedTile65536 2419958016 2420089088 14 6010 49193 31 _ _ (21607 / 1000) (2160703 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2420089088 :
    ThetaLowerSegment 2420089088 2420220160 (30250244325629 / 12500) (121007555571933 / 50000) := by
  exact
    packedTile65536 2420089088 2420220160 14 6089 49194 31 _ _ (1080353 / 50000) (2160709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2420220160 :
    ThetaLowerSegment 2420220160 2420351232 (121007555571933 / 50000) (48405657864051 / 20000) := by
  exact
    packedTile65536 2420220160 2420351232 14 6099 49195 31 _ _ (2160711 / 100000) (1080357 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2420351232 :
    ThetaLowerSegment 2420351232 2420482304 (48405657864051 / 20000)
      (242041240651959 / 100000) := by
  exact
    packedTile65536 2420351232 2420482304 14 5994 49197 31 _ _ (540179 / 25000) (2160719 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2420482304 :
    ThetaLowerSegment 2420482304 2420613376 (242041240651959 / 100000)
      (242054425377603 / 100000) := by
  exact
    packedTile65536 2420482304 2420613376 14 6102 49198 31 _ _ (1080361 / 50000) (86429 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2420613376 :
    ThetaLowerSegment 2420613376 2420744448 (242054425377603 / 100000)
      (121033769414883 / 50000) := by
  exact
    packedTile65536 2420613376 2420744448 14 6069 49199 31 _ _ (2160727 / 100000) (216073 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2420744448 :
    ThetaLowerSegment 2420744448 2420875520 (121033769414883 / 50000) (24208069337227 / 10000) := by
  exact
    packedTile65536 2420744448 2420875520 14 6088 49201 31 _ _ (2160733 / 100000) (67523 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2420875520 :
    ThetaLowerSegment 2420875520 2421006592 (24208069337227 / 10000) (60523431195787 / 25000) := by
  exact
    packedTile65536 2420875520 2421006592 14 6031 49202 31 _ _ (1080369 / 50000) (2160741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421006592 :
    ThetaLowerSegment 2421006592 2421137664 (60523431195787 / 25000) (48421350380539 / 20000) := by
  exact
    packedTile65536 2421006592 2421137664 14 6029 49203 31 _ _ (2160743 / 100000) (1080373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421137664 :
    ThetaLowerSegment 2421137664 2421268736 (48421350380539 / 20000) (48423943279339 / 20000) := by
  exact
    packedTile65536 2421137664 2421268736 14 6000 49205 31 _ _ (2160749 / 100000) (135047 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421268736 :
    ThetaLowerSegment 2421268736 2421399808 (48423943279339 / 20000) (48426551309417 / 20000) := by
  exact
    packedTile65536 2421268736 2421399808 14 6035 49206 31 _ _ (1080377 / 50000) (2160757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421399808 :
    ThetaLowerSegment 2421399808 2421530880 (48426551309417 / 20000) (48429166693321 / 20000) := by
  exact
    packedTile65536 2421399808 2421530880 14 6052 49207 31 _ _ (54019 / 2500) (2160763 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421530880 :
    ThetaLowerSegment 2421530880 2421661952 (48429166693321 / 20000) (9686359528157 / 4000) := by
  exact
    packedTile65536 2421530880 2421661952 14 6088 49209 31 _ _ (432153 / 20000) (67524 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421661952 :
    ThetaLowerSegment 2421661952 2421793024 (9686359528157 / 4000) (48434406554483 / 20000) := by
  exact
    packedTile65536 2421661952 2421793024 14 6037 49210 31 _ _ (216077 / 10000) (2160773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421793024 :
    ThetaLowerSegment 2421793024 2421924096 (48434406554483 / 20000)
      (242185155165063 / 100000) := by
  exact
    packedTile65536 2421793024 2421924096 14 6073 49211 31 _ _ (270097 / 12500) (2160779 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2421924096 :
    ThetaLowerSegment 2421924096 2422055168 (242185155165063 / 100000)
      (60549552110771 / 25000) := by
  exact
    packedTile65536 2421924096 2422055168 14 6041 49213 31 _ _ (2160781 / 100000) (135049 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422055168 :
    ThetaLowerSegment 2422055168 2422186240 (60549552110771 / 25000) (48442292109951 / 20000) := by
  exact
    packedTile65536 2422055168 2422186240 14 6133 49214 31 _ _ (2160787 / 100000) (216079 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422186240 :
    ThetaLowerSegment 2422186240 2422317312 (48442292109951 / 20000)
      (242224516055019 / 100000) := by
  exact
    packedTile65536 2422186240 2422317312 14 6042 49215 31 _ _ (270099 / 12500) (432159 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422317312 :
    ThetaLowerSegment 2422317312 2422448384 (242224516055019 / 100000)
      (242237610490899 / 100000) := by
  exact
    packedTile65536 2422317312 2422448384 14 6060 49217 31 _ _ (1080399 / 50000) (2160801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422448384 :
    ThetaLowerSegment 2422448384 2422579456 (242237610490899 / 100000) (6056264760863 / 2500) := by
  exact
    packedTile65536 2422448384 2422579456 14 6007 49218 31 _ _ (2160803 / 100000) (1080403 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422579456 :
    ThetaLowerSegment 2422579456 2422710528 (6056264760863 / 2500) (7570745623639 / 3125) := by
  exact
    packedTile65536 2422579456 2422710528 14 6141 49219 31 _ _ (270101 / 12500) (2160811 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422710528 :
    ThetaLowerSegment 2422710528 2422841600 (7570745623639 / 3125) (60569276436567 / 25000) := by
  exact
    packedTile65536 2422710528 2422841600 14 6130 49221 31 _ _ (1080407 / 50000) (2160817 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422841600 :
    ThetaLowerSegment 2422841600 2422972672 (60569276436567 / 25000) (60572504700153 / 25000) := by
  exact
    packedTile65536 2422841600 2422972672 14 5976 49222 31 _ _ (2160819 / 100000) (1080411 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2422972672 :
    ThetaLowerSegment 2422972672 2423103744 (60572504700153 / 25000) (60575815084053 / 25000) := by
  exact
    packedTile65536 2422972672 2423103744 14 6128 49223 31 _ _ (86433 / 4000) (540207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2423103744 :
    ThetaLowerSegment 2423103744 2423234816 (60575815084053 / 25000) (7572388118466 / 3125) := by
  exact
    packedTile65536 2423103744 2423234816 14 6090 49225 31 _ _ (216083 / 10000) (2160833 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2423234816 :
    ThetaLowerSegment 2423234816 2423365888 (7572388118466 / 3125) (121164755064671 / 50000) := by
  exact
    packedTile65536 2423234816 2423365888 14 6058 49226 31 _ _ (432167 / 20000) (1080419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2423365888 :
    ThetaLowerSegment 2423365888 2423496960 (121164755064671 / 50000)
      (242342918147747 / 100000) := by
  exact
    packedTile65536 2423365888 2423496960 14 6205 49227 31 _ _ (2160841 / 100000) (540211 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2423496960 :
    ThetaLowerSegment 2423496960 2423628032 (242342918147747 / 100000)
      (48471221158177 / 20000) := by
  exact
    packedTile65536 2423496960 2423628032 14 6103 49229 31 _ _ (1080423 / 50000) (2160849 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2423628032 :
    ThetaLowerSegment 2423628032 2423759104 (48471221158177 / 20000)
      (242369155176113 / 100000) := by
  exact
    packedTile65536 2423628032 2423759104 14 6039 49230 31 _ _ (540213 / 25000) (432171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2423759104 :
    ThetaLowerSegment 2423759104 2423890176 (242369155176113 / 100000)
      (121191130386909 / 50000) := by
  exact
    packedTile65536 2423759104 2423890176 14 6065 49231 31 _ _ (2160857 / 100000) (108043 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2423890176 :
    ThetaLowerSegment 2423890176 2424021248 (121191130386909 / 50000) (60598838359169 / 25000) := by
  exact
    packedTile65536 2423890176 2424021248 14 6059 49233 31 _ _ (1080431 / 50000) (432173 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424021248 :
    ThetaLowerSegment 2424021248 2424152320 (60598838359169 / 25000) (30301035778957 / 12500) := by
  exact
    packedTile65536 2424021248 2424152320 14 5985 49234 31 _ _ (540217 / 25000) (2160871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424152320 :
    ThetaLowerSegment 2424152320 2424283392 (30301035778957 / 12500)
      (242421448109099 / 100000) := by
  exact
    packedTile65536 2424152320 2424283392 14 6091 49235 31 _ _ (2160873 / 100000) (540219 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424283392 :
    ThetaLowerSegment 2424283392 2424414464 (242421448109099 / 100000)
      (121217276920117 / 50000) := by
  exact
    packedTile65536 2424283392 2424414464 14 6065 49237 31 _ _ (2160879 / 100000) (1080441 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424414464 :
    ThetaLowerSegment 2424414464 2424545536 (121217276920117 / 50000) (24244777628943 / 10000) := by
  exact
    packedTile65536 2424414464 2424545536 14 6119 49238 31 _ _ (540221 / 25000) (2160887 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424545536 :
    ThetaLowerSegment 2424545536 2424676608 (24244777628943 / 10000) (30307601886707 / 12500) := by
  exact
    packedTile65536 2424545536 2424676608 14 6034 49239 31 _ _ (2160889 / 100000) (540223 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424676608 :
    ThetaLowerSegment 2424676608 2424807680 (30307601886707 / 12500)
      (242473899312881 / 100000) := by
  exact
    packedTile65536 2424676608 2424807680 14 6055 49241 31 _ _ (432179 / 20000) (1080449 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424807680 :
    ThetaLowerSegment 2424807680 2424938752 (242473899312881 / 100000)
      (242487128342681 / 100000) := by
  exact
    packedTile65536 2424807680 2424938752 14 6122 49242 31 _ _ (21609 / 1000) (2160903 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2424938752 :
    ThetaLowerSegment 2424938752 2425069824 (242487128342681 / 100000)
      (242500348765589 / 100000) := by
  exact
    packedTile65536 2424938752 2425069824 14 6118 49243 31 _ _ (1080453 / 50000) (2160909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425069824 :
    ThetaLowerSegment 2425069824 2425200896 (242500348765589 / 100000)
      (60628398247277 / 25000) := by
  exact
    packedTile65536 2425069824 2425200896 14 6129 49244 31 _ _ (2160911 / 100000) (1080457 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425200896 :
    ThetaLowerSegment 2425200896 2425331968 (60628398247277 / 25000) (48505363992413 / 20000) := by
  exact
    packedTile65536 2425200896 2425331968 14 6121 49246 31 _ _ (2160917 / 100000) (54023 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425331968 :
    ThetaLowerSegment 2425331968 2425463040 (48505363992413 / 20000)
      (242539826551583 / 100000) := by
  exact
    packedTile65536 2425331968 2425463040 14 6019 49247 31 _ _ (1080461 / 50000) (86437 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425463040 :
    ThetaLowerSegment 2425463040 2425594112 (242539826551583 / 100000) (7579780088338 / 3125) := by
  exact
    packedTile65536 2425463040 2425594112 14 6079 49248 31 _ _ (2160927 / 100000) (216093 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425594112 :
    ThetaLowerSegment 2425594112 2425725184 (7579780088338 / 3125) (15160374848417 / 6250) := by
  exact
    packedTile65536 2425594112 2425725184 14 6032 49250 31 _ _ (2160933 / 100000) (270117 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425725184 :
    ThetaLowerSegment 2425725184 2425856256 (15160374848417 / 6250) (121289553992759 / 50000) := by
  exact
    packedTile65536 2425725184 2425856256 14 6067 49251 31 _ _ (1080469 / 50000) (2160941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425856256 :
    ThetaLowerSegment 2425856256 2425987328 (121289553992759 / 50000)
      (121296114618743 / 50000) := by
  exact
    packedTile65536 2425856256 2425987328 14 6072 49252 31 _ _ (135059 / 6250) (2160947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2425987328 :
    ThetaLowerSegment 2425987328 2426118400 (121296114618743 / 50000)
      (121302653650417 / 50000) := by
  exact
    packedTile65536 2425987328 2426118400 14 6052 49254 31 _ _ (2160949 / 100000) (270119 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2426118400 :
    ThetaLowerSegment 2426118400 2426249472 (121302653650417 / 50000) (60654624981251 / 25000) := by
  exact
    packedTile65536 2426118400 2426249472 14 6105 49255 31 _ _ (1080477 / 50000) (2160957 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2426249472 :
    ThetaLowerSegment 2426249472 2426380544 (60654624981251 / 25000) (60657902077091 / 25000) := by
  exact
    packedTile65536 2426249472 2426380544 14 6066 49256 31 _ _ (13506 / 625) (2160963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2426380544 :
    ThetaLowerSegment 2426380544 2426511616 (60657902077091 / 25000)
      (242644679985649 / 100000) := by
  exact
    packedTile65536 2426380544 2426511616 14 6049 49258 31 _ _ (432193 / 20000) (270121 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2426511616 :
    ThetaLowerSegment 2426511616 2426642688 (242644679985649 / 100000)
      (242657905128169 / 100000) := by
  exact
    packedTile65536 2426511616 2426642688 14 6120 49259 31 _ _ (2160971 / 100000) (1080487 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2426642688 :
    ThetaLowerSegment 2426642688 2426773760 (242657905128169 / 100000)
      (242671225384233 / 100000) := by
  exact
    packedTile65536 2426642688 2426773760 14 6164 49260 31 _ _ (135061 / 6250) (2160979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2426773760 :
    ThetaLowerSegment 2426773760 2426904832 (242671225384233 / 100000) (9707366094903 / 4000) := by
  exact
    packedTile65536 2426773760 2426904832 14 5982 49262 31 _ _ (2160981 / 100000) (270123 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2426904832 :
    ThetaLowerSegment 2426904832 2427035904 (9707366094903 / 4000) (121348668277131 / 50000) := by
  exact
    packedTile65536 2426904832 2427035904 14 6101 49263 31 _ _ (2160987 / 100000) (216099 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427035904 :
    ThetaLowerSegment 2427035904 2427166976 (121348668277131 / 50000) (24271040839487 / 10000) := by
  exact
    packedTile65536 2427035904 2427166976 14 6049 49264 31 _ _ (67531 / 3125) (432199 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427166976 :
    ThetaLowerSegment 2427166976 2427298048 (24271040839487 / 10000) (4854472241853 / 2000) := by
  exact
    packedTile65536 2427166976 2427298048 14 6110 49266 31 _ _ (1080499 / 50000) (2161001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427298048 :
    ThetaLowerSegment 2427298048 2427429120 (4854472241853 / 2000) (7585523603528 / 3125) := by
  exact
    packedTile65536 2427298048 2427429120 14 6082 49267 31 _ _ (2161003 / 100000) (1080503 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427429120 :
    ThetaLowerSegment 2427429120 2427560192 (7585523603528 / 3125) (15171867984907 / 6250) := by
  exact
    packedTile65536 2427429120 2427560192 14 6077 49268 31 _ _ (135063 / 6250) (2161011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427560192 :
    ThetaLowerSegment 2427560192 2427691264 (15171867984907 / 6250) (60690777210541 / 25000) := by
  exact
    packedTile65536 2427560192 2427691264 14 6118 49270 31 _ _ (1080507 / 50000) (2161017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427691264 :
    ThetaLowerSegment 2427691264 2427822336 (60690777210541 / 25000) (121387983452607 / 50000) := by
  exact
    packedTile65536 2427691264 2427822336 14 5950 49271 31 _ _ (2161019 / 100000) (1080511 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427822336 :
    ThetaLowerSegment 2427822336 2427953408 (121387983452607 / 50000)
      (242789077843889 / 100000) := by
  exact
    packedTile65536 2427822336 2427953408 14 6067 49272 31 _ _ (86441 / 4000) (540257 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2427953408 :
    ThetaLowerSegment 2427953408 2428084480 (242789077843889 / 100000)
      (242802098049639 / 100000) := by
  exact
    packedTile65536 2427953408 2428084480 14 6025 49274 31 _ _ (216103 / 10000) (2161033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2428084480 :
    ThetaLowerSegment 2428084480 2428215552 (242802098049639 / 100000)
      (242815250108649 / 100000) := by
  exact
    packedTile65536 2428084480 2428215552 14 6086 49275 31 _ _ (432207 / 20000) (1080519 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2428215552 :
    ThetaLowerSegment 2428215552 2428346624 (242815250108649 / 100000)
      (242828168811747 / 100000) := by
  exact
    packedTile65536 2428215552 2428346624 14 5978 49276 31 _ _ (2161041 / 100000) (540261 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2428346624 :
    ThetaLowerSegment 2428346624 2428477696 (242828168811747 / 100000)
      (48568280179281 / 20000) := by
  exact
    packedTile65536 2428346624 2428477696 14 6123 49278 31 _ _ (1080523 / 50000) (2161049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2428477696 :
    ThetaLowerSegment 2428477696 2428608768 (48568280179281 / 20000)
      (242854537931513 / 100000) := by
  exact
    packedTile65536 2428477696 2428608768 14 6079 49279 31 _ _ (540263 / 25000) (432211 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2428608768 :
    ThetaLowerSegment 2428608768 2428739840 (242854537931513 / 100000)
      (242867720379213 / 100000) := by
  exact
    packedTile65536 2428608768 2428739840 14 6100 49280 31 _ _ (2161057 / 100000) (108053 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2428739840 :
    ThetaLowerSegment 2428739840 2428870912 (242867720379213 / 100000)
      (48576144265641 / 20000) := by
  exact
    packedTile65536 2428739840 2428870912 14 6016 49282 31 _ _ (1080531 / 50000) (432213 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2428870912 :
    ThetaLowerSegment 2428870912 2429001984 (48576144265641 / 20000) (48578746191513 / 20000) := by
  exact
    packedTile65536 2428870912 2429001984 14 6020 49283 31 _ _ (540267 / 25000) (2161071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429001984 :
    ThetaLowerSegment 2429001984 2429133056 (48578746191513 / 20000)
      (242906779516339 / 100000) := by
  exact
    packedTile65536 2429001984 2429133056 14 6038 49284 31 _ _ (2161073 / 100000) (540269 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429133056 :
    ThetaLowerSegment 2429133056 2429264128 (242906779516339 / 100000)
      (30364977703513 / 12500) := by
  exact
    packedTile65536 2429133056 2429264128 14 6035 49286 31 _ _ (2161079 / 100000) (1080541 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429264128 :
    ThetaLowerSegment 2429264128 2429395200 (30364977703513 / 12500) (3036663471467 / 1250) := by
  exact
    packedTile65536 2429264128 2429395200 14 6134 49287 31 _ _ (540271 / 25000) (2161087 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429395200 :
    ThetaLowerSegment 2429395200 2429526272 (3036663471467 / 1250) (24294619552759 / 10000) := by
  exact
    packedTile65536 2429395200 2429526272 14 6070 49288 31 _ _ (2161089 / 100000) (540273 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429526272 :
    ThetaLowerSegment 2429526272 2429657344 (24294619552759 / 10000) (48591858784877 / 20000) := by
  exact
    packedTile65536 2429526272 2429657344 14 6061 49290 31 _ _ (432219 / 20000) (1080549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429657344 :
    ThetaLowerSegment 2429657344 2429788416 (48591858784877 / 20000) (48594490140237 / 20000) := by
  exact
    packedTile65536 2429657344 2429788416 14 6088 49291 31 _ _ (21611 / 1000) (2161103 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429788416 :
    ThetaLowerSegment 2429788416 2429919488 (48594490140237 / 20000) (48597105078497 / 20000) := by
  exact
    packedTile65536 2429788416 2429919488 14 6050 49292 31 _ _ (1080553 / 50000) (2161109 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2429919488 :
    ThetaLowerSegment 2429919488 2430050560 (48597105078497 / 20000) (60749627877121 / 25000) := by
  exact
    packedTile65536 2429919488 2430050560 14 6009 49294 31 _ _ (2161111 / 100000) (1080557 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430050560 :
    ThetaLowerSegment 2430050560 2430181632 (60749627877121 / 25000) (607529241193 / 250) := by
  exact
    packedTile65536 2430050560 2430181632 14 6101 49295 31 _ _ (540279 / 25000) (2161119 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430181632 :
    ThetaLowerSegment 2430181632 2430312704 (607529241193 / 250) (121512349974137 / 50000) := by
  exact
    packedTile65536 2430181632 2430312704 14 6017 49296 31 _ _ (1080561 / 50000) (17289 / 800)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430312704 :
    ThetaLowerSegment 2430312704 2430443776 (121512349974137 / 50000) (2430377488331 / 1000) := by
  exact
    packedTile65536 2430312704 2430443776 14 6038 49298 31 _ _ (2161127 / 100000) (216113 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430443776 :
    ThetaLowerSegment 2430443776 2430574848 (2430377488331 / 1000) (60762755626461 / 25000) := by
  exact
    packedTile65536 2430443776 2430574848 14 6142 49299 31 _ _ (540283 / 25000) (432227 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430574848 :
    ThetaLowerSegment 2430574848 2430705920 (60762755626461 / 25000) (30383012173843 / 12500) := by
  exact
    packedTile65536 2430574848 2430705920 14 6050 49300 31 _ _ (1080569 / 50000) (2161141 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430705920 :
    ThetaLowerSegment 2430705920 2430836992 (30383012173843 / 12500) (48615450453637 / 20000) := by
  exact
    packedTile65536 2430705920 2430836992 14 6087 49302 31 _ _ (2161143 / 100000) (1080573 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430836992 :
    ThetaLowerSegment 2430836992 2430968064 (48615450453637 / 20000) (121545149562349 / 50000) := by
  exact
    packedTile65536 2430836992 2430968064 14 6037 49303 31 _ _ (2161149 / 100000) (67536 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2430968064 :
    ThetaLowerSegment 2430968064 2431099136 (121545149562349 / 50000)
      (121551671925121 / 50000) := by
  exact
    packedTile65536 2430968064 2431099136 14 6036 49304 31 _ _ (1080577 / 50000) (2161157 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2431099136 :
    ThetaLowerSegment 2431099136 2431230208 (121551671925121 / 50000) (48623265186471 / 20000) := by
  exact
    packedTile65536 2431099136 2431230208 14 6007 49306 31 _ _ (2161159 / 100000) (1080581 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2431230208 :
    ThetaLowerSegment 2431230208 2431361280 (48623265186471 / 20000) (3039118349709 / 1250) := by
  exact
    packedTile65536 2431230208 2431361280 14 6081 49307 31 _ _ (432233 / 20000) (135073 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2431361280 :
    ThetaLowerSegment 2431361280 2431492352 (3039118349709 / 1250) (24314263166319 / 10000) := by
  exact
    packedTile65536 2431361280 2431492352 14 6091 49308 31 _ _ (216117 / 10000) (2161173 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2431492352 :
    ThetaLowerSegment 2431492352 2431623424 (24314263166319 / 10000) (121577868517227 / 50000) := by
  exact
    packedTile65536 2431492352 2431623424 14 6064 49310 31 _ _ (270147 / 12500) (2161179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2431623424 :
    ThetaLowerSegment 2431623424 2431754496 (121577868517227 / 50000)
      (121584425540381 / 50000) := by
  exact
    packedTile65536 2431623424 2431754496 14 6068 49311 31 _ _ (2161181 / 100000) (67537 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2431754496 :
    ThetaLowerSegment 2431754496 2431885568 (121584425540381 / 50000)
      (121590904776009 / 50000) := by
  exact
    packedTile65536 2431754496 2431885568 14 5996 49312 31 _ _ (1080593 / 50000) (2161189 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2431885568 :
    ThetaLowerSegment 2431885568 2432016640 (121590904776009 / 50000) (24319501659633 / 10000) := by
  exact
    packedTile65536 2431885568 2432016640 14 6111 49314 31 _ _ (270149 / 12500) (432239 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432016640 :
    ThetaLowerSegment 2432016640 2432147712 (24319501659633 / 10000)
      (243208011873891 / 100000) := by
  exact
    packedTile65536 2432016640 2432147712 14 6013 49315 31 _ _ (2161197 / 100000) (5403 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432147712 :
    ThetaLowerSegment 2432147712 2432278784 (243208011873891 / 100000)
      (30402654534381 / 12500) := by
  exact
    packedTile65536 2432147712 2432278784 14 6119 49316 31 _ _ (2161203 / 100000) (1080603 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432278784 :
    ThetaLowerSegment 2432278784 2432409856 (30402654534381 / 12500) (30404285165817 / 12500) := by
  exact
    packedTile65536 2432278784 2432409856 14 6036 49318 31 _ _ (270151 / 12500) (2161211 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432409856 :
    ThetaLowerSegment 2432409856 2432540928 (30404285165817 / 12500)
      (243247389083381 / 100000) := by
  exact
    packedTile65536 2432409856 2432540928 14 6065 49319 31 _ _ (2161213 / 100000) (67538 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432540928 :
    ThetaLowerSegment 2432540928 2432672000 (243247389083381 / 100000)
      (121630332725849 / 50000) := by
  exact
    packedTile65536 2432540928 2432672000 14 6143 49320 31 _ _ (2161219 / 100000) (1080611 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432672000 :
    ThetaLowerSegment 2432672000 2432803072 (121630332725849 / 50000)
      (121636821800909 / 50000) := by
  exact
    packedTile65536 2432672000 2432803072 14 6005 49322 31 _ _ (270153 / 12500) (2161227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432803072 :
    ThetaLowerSegment 2432803072 2432934144 (121636821800909 / 50000)
      (121643361679863 / 50000) := by
  exact
    packedTile65536 2432803072 2432934144 14 6052 49323 31 _ _ (2161229 / 100000) (135077 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2432934144 :
    ThetaLowerSegment 2432934144 2433065216 (121643361679863 / 50000)
      (121649975058963 / 50000) := by
  exact
    packedTile65536 2432934144 2433065216 14 6120 49324 31 _ _ (432247 / 20000) (1080619 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433065216 :
    ThetaLowerSegment 2433065216 2433196288 (121649975058963 / 50000)
      (121656538744843 / 50000) := by
  exact
    packedTile65536 2433065216 2433196288 14 6074 49326 31 _ _ (54031 / 2500) (2161243 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433196288 :
    ThetaLowerSegment 2433196288 2433327360 (121656538744843 / 50000)
      (121663169447571 / 50000) := by
  exact
    packedTile65536 2433196288 2433327360 14 6136 49327 31 _ _ (1080623 / 50000) (2161249 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433327360 :
    ThetaLowerSegment 2433327360 2433458432 (121663169447571 / 50000)
      (243339317207397 / 100000) := by
  exact
    packedTile65536 2433327360 2433458432 14 6005 49328 31 _ _ (2161251 / 100000) (1080627 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433458432 :
    ThetaLowerSegment 2433458432 2433589504 (243339317207397 / 100000) (9734096836101 / 4000) := by
  exact
    packedTile65536 2433458432 2433589504 14 6063 49330 31 _ _ (270157 / 12500) (2161259 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433589504 :
    ThetaLowerSegment 2433589504 2433720576 (9734096836101 / 4000) (243365343088023 / 100000) := by
  exact
    packedTile65536 2433589504 2433720576 14 5979 49331 31 _ _ (1080631 / 50000) (432253 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433720576 :
    ThetaLowerSegment 2433720576 2433851648 (243365343088023 / 100000)
      (121689216941121 / 50000) := by
  exact
    packedTile65536 2433720576 2433851648 14 6057 49332 31 _ _ (2161267 / 100000) (216127 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433851648 :
    ThetaLowerSegment 2433851648 2433982720 (121689216941121 / 50000)
      (243391736517557 / 100000) := by
  exact
    packedTile65536 2433851648 2433982720 14 6155 49334 31 _ _ (2161273 / 100000) (540319 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2433982720 :
    ThetaLowerSegment 2433982720 2434113792 (243391736517557 / 100000)
      (48680949914479 / 20000) := by
  exact
    packedTile65536 2433982720 2434113792 14 6021 49335 31 _ _ (1080639 / 50000) (2161281 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434113792 :
    ThetaLowerSegment 2434113792 2434244864 (48680949914479 / 20000) (30427236001469 / 12500) := by
  exact
    packedTile65536 2434113792 2434244864 14 6079 49336 31 _ _ (2161283 / 100000) (1080643 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434244864 :
    ThetaLowerSegment 2434244864 2434375936 (30427236001469 / 12500)
      (243431164810079 / 100000) := by
  exact
    packedTile65536 2434244864 2434375936 14 6143 49338 31 _ _ (2161289 / 100000) (540323 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434375936 :
    ThetaLowerSegment 2434375936 2434507008 (243431164810079 / 100000)
      (48688789340559 / 20000) := by
  exact
    packedTile65536 2434375936 2434507008 14 5914 49339 31 _ _ (1080647 / 50000) (2161297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434507008 :
    ThetaLowerSegment 2434507008 2434638080 (48688789340559 / 20000) (48691376416659 / 20000) := by
  exact
    packedTile65536 2434507008 2434638080 14 5985 49340 31 _ _ (21613 / 1000) (2161303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434638080 :
    ThetaLowerSegment 2434638080 2434769152 (48691376416659 / 20000) (48694031363721 / 20000) := by
  exact
    packedTile65536 2434638080 2434769152 14 6142 49342 31 _ _ (432261 / 20000) (540327 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434769152 :
    ThetaLowerSegment 2434769152 2434900224 (48694031363721 / 20000) (9739329482669 / 4000) := by
  exact
    packedTile65536 2434769152 2434900224 14 6052 49343 31 _ _ (216131 / 10000) (2161313 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2434900224 :
    ThetaLowerSegment 2434900224 2435031296 (9739329482669 / 4000) (243496310867209 / 100000) := by
  exact
    packedTile65536 2434900224 2435031296 14 6049 49344 31 _ _ (540329 / 25000) (2161319 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435031296 :
    ThetaLowerSegment 2435031296 2435162368 (243496310867209 / 100000)
      (243509347955481 / 100000) := by
  exact
    packedTile65536 2435031296 2435162368 14 6032 49346 31 _ _ (2161321 / 100000) (540331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435162368 :
    ThetaLowerSegment 2435162368 2435293440 (243509347955481 / 100000)
      (243522242426397 / 100000) := by
  exact
    packedTile65536 2435162368 2435293440 14 5966 49347 31 _ _ (1080663 / 50000) (2161329 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435293440 :
    ThetaLowerSegment 2435293440 2435424512 (243522242426397 / 100000)
      (243535545424857 / 100000) := by
  exact
    packedTile65536 2435293440 2435424512 14 6155 49348 31 _ _ (540333 / 25000) (432267 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435424512 :
    ThetaLowerSegment 2435424512 2435555584 (243535545424857 / 100000)
      (243548733903231 / 100000) := by
  exact
    packedTile65536 2435424512 2435555584 14 6102 49350 31 _ _ (2161337 / 100000) (108067 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435555584 :
    ThetaLowerSegment 2435555584 2435686656 (243548733903231 / 100000)
      (30445231927073 / 12500) := by
  exact
    packedTile65536 2435555584 2435686656 14 6071 49351 31 _ _ (2161343 / 100000) (1080673 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435686656 :
    ThetaLowerSegment 2435686656 2435817728 (30445231927073 / 12500) (6089372316693 / 2500) := by
  exact
    packedTile65536 2435686656 2435817728 14 6032 49352 31 _ _ (540337 / 25000) (2161351 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435817728 :
    ThetaLowerSegment 2435817728 2435948800 (6089372316693 / 2500) (24358783917219 / 10000) := by
  exact
    packedTile65536 2435817728 2435948800 14 5990 49354 31 _ _ (2161353 / 100000) (540339 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2435948800 :
    ThetaLowerSegment 2435948800 2436079872 (24358783917219 / 10000) (121800455535711 / 50000) := by
  exact
    packedTile65536 2435948800 2436079872 14 6048 49355 31 _ _ (2161359 / 100000) (1080681 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436079872 :
    ThetaLowerSegment 2436079872 2436210944 (121800455535711 / 50000)
      (121806945031121 / 50000) := by
  exact
    packedTile65536 2436079872 2436210944 14 6005 49356 31 _ _ (540341 / 25000) (2161367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436210944 :
    ThetaLowerSegment 2436210944 2436342016 (121806945031121 / 50000) (30453376196509 / 12500) := by
  exact
    packedTile65536 2436210944 2436342016 14 6070 49357 31 _ _ (2161369 / 100000) (540343 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436342016 :
    ThetaLowerSegment 2436342016 2436473088 (30453376196509 / 12500) (30455010196009 / 12500) := by
  exact
    packedTile65536 2436342016 2436473088 14 6048 49359 31 _ _ (17291 / 800) (1080689 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436473088 :
    ThetaLowerSegment 2436473088 2436604160 (30455010196009 / 12500) (15228333176717 / 6250) := by
  exact
    packedTile65536 2436473088 2436604160 14 6130 49360 31 _ _ (108069 / 5000) (2161383 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436604160 :
    ThetaLowerSegment 2436604160 2436735232 (15228333176717 / 6250) (60916632062597 / 25000) := by
  exact
    packedTile65536 2436604160 2436735232 14 6106 49361 31 _ _ (1080693 / 50000) (2161389 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436735232 :
    ThetaLowerSegment 2436735232 2436866304 (60916632062597 / 25000)
      (243679732188007 / 100000) := by
  exact
    packedTile65536 2436735232 2436866304 14 6109 49363 31 _ _ (2161391 / 100000) (1080697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436866304 :
    ThetaLowerSegment 2436866304 2436997376 (243679732188007 / 100000)
      (243692715693779 / 100000) := by
  exact
    packedTile65536 2436866304 2436997376 14 6007 49364 31 _ _ (540349 / 25000) (2161399 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2436997376 :
    ThetaLowerSegment 2436997376 2437128448 (243692715693779 / 100000)
      (243705984540657 / 100000) := by
  exact
    packedTile65536 2436997376 2437128448 14 6139 49365 31 _ _ (1080701 / 50000) (432281 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2437128448 :
    ThetaLowerSegment 2437128448 2437259520 (243705984540657 / 100000)
      (60929779852749 / 25000) := by
  exact
    packedTile65536 2437128448 2437259520 14 6077 49367 31 _ _ (2161407 / 100000) (216141 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2437259520 :
    ThetaLowerSegment 2437259520 2437390592 (60929779852749 / 25000) (60933060877683 / 25000) := by
  exact
    packedTile65536 2437259520 2437390592 14 6072 49368 31 _ _ (2161413 / 100000) (270177 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2437390592 :
    ThetaLowerSegment 2437390592 2437521664 (60933060877683 / 25000) (24374527902269 / 10000) := by
  exact
    packedTile65536 2437390592 2437521664 14 6031 49369 31 _ _ (1080709 / 50000) (2161421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2437521664 :
    ThetaLowerSegment 2437521664 2437652736 (24374527902269 / 10000) (48751694902021 / 20000) := by
  exact
    packedTile65536 2437521664 2437652736 14 6105 49371 31 _ _ (2161423 / 100000) (1080713 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2437652736 :
    ThetaLowerSegment 2437652736 2437783808 (48751694902021 / 20000)
      (243771607352709 / 100000) := by
  exact
    packedTile65536 2437652736 2437783808 14 6076 49372 31 _ _ (2161429 / 100000) (270179 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2437783808 :
    ThetaLowerSegment 2437783808 2437914880 (243771607352709 / 100000)
      (243784807230147 / 100000) := by
  exact
    packedTile65536 2437783808 2437914880 14 6107 49373 31 _ _ (1080717 / 50000) (2161437 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2437914880 :
    ThetaLowerSegment 2437914880 2438045952 (243784807230147 / 100000)
      (121898953855963 / 50000) := by
  exact
    packedTile65536 2437914880 2438045952 14 6061 49375 31 _ _ (2161439 / 100000) (1080721 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438045952 :
    ThetaLowerSegment 2438045952 2438177024 (121898953855963 / 50000)
      (243810999584291 / 100000) := by
  exact
    packedTile65536 2438045952 2438177024 14 6057 49376 31 _ _ (432289 / 20000) (270181 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438177024 :
    ThetaLowerSegment 2438177024 2438308096 (243810999584291 / 100000)
      (243824093648391 / 100000) := by
  exact
    packedTile65536 2438177024 2438308096 14 6058 49377 31 _ _ (43229 / 2000) (2161453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438308096 :
    ThetaLowerSegment 2438308096 2438439168 (243824093648391 / 100000)
      (243837267722711 / 100000) := by
  exact
    packedTile65536 2438308096 2438439168 14 6095 49379 31 _ _ (135091 / 6250) (2161459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438439168 :
    ThetaLowerSegment 2438439168 2438570240 (243837267722711 / 100000)
      (243850409405591 / 100000) := by
  exact
    packedTile65536 2438439168 2438570240 14 6080 49380 31 _ _ (2161461 / 100000) (270183 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438570240 :
    ThetaLowerSegment 2438570240 2438701312 (243850409405591 / 100000)
      (48772711952947 / 20000) := by
  exact
    packedTile65536 2438570240 2438701312 14 6084 49381 31 _ _ (1080733 / 50000) (2161469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438701312 :
    ThetaLowerSegment 2438701312 2438832384 (48772711952947 / 20000)
      (243876494013183 / 100000) := by
  exact
    packedTile65536 2438701312 2438832384 14 5984 49383 31 _ _ (67546 / 3125) (86459 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438832384 :
    ThetaLowerSegment 2438832384 2438963456 (243876494013183 / 100000) (1524309967033 / 625) := by
  exact
    packedTile65536 2438832384 2438963456 14 6061 49384 31 _ _ (2161477 / 100000) (54037 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2438963456 :
    ThetaLowerSegment 2438963456 2439094528 (1524309967033 / 625) (121951390963481 / 50000) := by
  exact
    packedTile65536 2438963456 2439094528 14 6101 49385 31 _ _ (1080741 / 50000) (432297 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2439094528 :
    ThetaLowerSegment 2439094528 2439225600 (121951390963481 / 50000) (24391604481733 / 10000) := by
  exact
    packedTile65536 2439094528 2439225600 14 6136 49387 31 _ _ (135093 / 6250) (2161491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2439225600 :
    ThetaLowerSegment 2439225600 2439356672 (24391604481733 / 10000)
      (243929223440151 / 100000) := by
  exact
    packedTile65536 2439225600 2439356672 14 6097 49388 31 _ _ (2161493 / 100000) (270187 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2439356672 :
    ThetaLowerSegment 2439356672 2439487744 (243929223440151 / 100000)
      (30492792156823 / 12500) := by
  exact
    packedTile65536 2439356672 2439487744 14 6067 49389 31 _ _ (2161499 / 100000) (1080751 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2439487744 :
    ThetaLowerSegment 2439487744 2439618816 (30492792156823 / 12500) (30494414905951 / 12500) := by
  exact
    packedTile65536 2439487744 2439618816 14 6006 49391 31 _ _ (67547 / 3125) (2161507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2439618816 :
    ThetaLowerSegment 2439618816 2439749888 (30494414905951 / 12500) (121984176573439 / 50000) := by
  exact
    packedTile65536 2439618816 2439749888 14 6030 49392 31 _ _ (2161509 / 100000) (270189 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2439749888 :
    ThetaLowerSegment 2439749888 2439880960 (121984176573439 / 50000)
      (121990838362669 / 50000) := by
  exact
    packedTile65536 2439749888 2439880960 14 6164 49393 31 _ _ (432303 / 20000) (1080759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2439880960 :
    ThetaLowerSegment 2439880960 2440012032 (121990838362669 / 50000)
      (121997507732629 / 50000) := by
  exact
    packedTile65536 2439880960 2440012032 14 6171 49395 31 _ _ (27019 / 1250) (2161523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440012032 :
    ThetaLowerSegment 2440012032 2440143104 (121997507732629 / 50000)
      (244008060268633 / 100000) := by
  exact
    packedTile65536 2440012032 2440143104 14 6035 49396 31 _ _ (86461 / 4000) (270191 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440143104 :
    ThetaLowerSegment 2440143104 2440274176 (244008060268633 / 100000)
      (244021258576919 / 100000) := by
  exact
    packedTile65536 2440143104 2440274176 14 6106 49397 31 _ _ (2161531 / 100000) (1080767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440274176 :
    ThetaLowerSegment 2440274176 2440405248 (244021258576919 / 100000)
      (244034409361943 / 100000) := by
  exact
    packedTile65536 2440274176 2440405248 14 6084 49399 31 _ _ (67548 / 3125) (2161539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440405248 :
    ThetaLowerSegment 2440405248 2440536320 (244034409361943 / 100000) (7626485242321 / 3125) := by
  exact
    packedTile65536 2440405248 2440536320 14 6069 49400 31 _ _ (2161541 / 100000) (270193 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440536320 :
    ThetaLowerSegment 2440536320 2440667392 (7626485242321 / 3125) (244060481905443 / 100000) := by
  exact
    packedTile65536 2440536320 2440667392 14 5993 49401 31 _ _ (2161547 / 100000) (43231 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440667392 :
    ThetaLowerSegment 2440667392 2440798464 (244060481905443 / 100000)
      (244073444732787 / 100000) := by
  exact
    packedTile65536 2440667392 2440798464 14 5997 49403 31 _ _ (135097 / 6250) (432311 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440798464 :
    ThetaLowerSegment 2440798464 2440929536 (244073444732787 / 100000)
      (244086550258941 / 100000) := by
  exact
    packedTile65536 2440798464 2440929536 14 6063 49404 31 _ _ (1080779 / 50000) (2161561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2440929536 :
    ThetaLowerSegment 2440929536 2441060608 (244086550258941 / 100000)
      (122049923016477 / 50000) := by
  exact
    packedTile65536 2440929536 2441060608 14 6151 49405 31 _ _ (2161563 / 100000) (1080783 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441060608 :
    ThetaLowerSegment 2441060608 2441191680 (122049923016477 / 50000)
      (122056443386349 / 50000) := by
  exact
    packedTile65536 2441060608 2441191680 14 6033 49407 31 _ _ (67549 / 3125) (2161571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441191680 :
    ThetaLowerSegment 2441191680 2441322752 (122056443386349 / 50000)
      (122062999440291 / 50000) := by
  exact
    packedTile65536 2441191680 2441322752 14 6066 49408 31 _ _ (1080787 / 50000) (2161577 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441322752 :
    ThetaLowerSegment 2441322752 2441339136 (122062999440291 / 50000)
      (122063807870837 / 50000) := by
  exact
    packedTile65536 2441322752 2441339136 11 748 49409 31 _ _ (2161579 / 100000) (1080791 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441339136 :
    ThetaLowerSegment 2441339136 2441341184 (122063807870837 / 50000)
      (122063898657197 / 50000) := by
  exact
    packedTile65536 2441339136 2441341184 8 84 49409 31 _ _ (108079 / 5000) (2161583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2409341184_2441341184 :
    ThetaLowerSegment 2409341184 2441341184 (120463607486549 / 50000)
      (122063898657197 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2409341184 cell2409472256)
                  (ThetaLowerSegment.join cell2409603328 cell2409734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2409865472 cell2409996544)
                  (ThetaLowerSegment.join cell2410127616 cell2410258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2410389760 cell2410520832)
                  (ThetaLowerSegment.join cell2410651904 cell2410782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2410914048 cell2411045120)
                  (ThetaLowerSegment.join cell2411176192 cell2411307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2411438336 cell2411569408)
                  (ThetaLowerSegment.join cell2411700480 cell2411831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2411962624 cell2412093696)
                  (ThetaLowerSegment.join cell2412224768 cell2412355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2412486912 cell2412617984)
                  (ThetaLowerSegment.join cell2412749056 cell2412880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2413011200 cell2413142272)
                  (ThetaLowerSegment.join cell2413273344 cell2413404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2413535488 cell2413666560)
                  (ThetaLowerSegment.join cell2413797632 cell2413928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2414059776 cell2414190848)
                  (ThetaLowerSegment.join cell2414321920 cell2414452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2414584064 cell2414715136)
                  (ThetaLowerSegment.join cell2414846208 cell2414977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2415108352 cell2415239424)
                  (ThetaLowerSegment.join cell2415370496 cell2415501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2415632640 cell2415763712)
                  (ThetaLowerSegment.join cell2415894784 cell2416025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2416156928 cell2416288000)
                  (ThetaLowerSegment.join cell2416419072 cell2416550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2416681216 cell2416812288)
                  (ThetaLowerSegment.join cell2416943360 cell2417074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2417205504 cell2417336576)
                  (ThetaLowerSegment.join cell2417467648 cell2417598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2417729792 cell2417860864)
                  (ThetaLowerSegment.join cell2417991936 cell2418123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2418254080 cell2418385152)
                  (ThetaLowerSegment.join cell2418516224 cell2418647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2418778368 cell2418909440)
                  (ThetaLowerSegment.join cell2419040512 cell2419171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2419302656 cell2419433728)
                  (ThetaLowerSegment.join cell2419564800 cell2419695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2419826944 cell2419958016)
                  (ThetaLowerSegment.join cell2420089088 cell2420220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2420351232 cell2420482304)
                  (ThetaLowerSegment.join cell2420613376 cell2420744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2420875520 cell2421006592)
                  (ThetaLowerSegment.join cell2421137664 cell2421268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2421399808 cell2421530880)
                  (ThetaLowerSegment.join cell2421661952 cell2421793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2421924096 cell2422055168)
                  (ThetaLowerSegment.join cell2422186240 cell2422317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2422448384 cell2422579456)
                  (ThetaLowerSegment.join cell2422710528 cell2422841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2422972672 cell2423103744)
                  (ThetaLowerSegment.join cell2423234816 cell2423365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2423496960 cell2423628032)
                  (ThetaLowerSegment.join cell2423759104 cell2423890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2424021248 cell2424152320)
                  (ThetaLowerSegment.join cell2424283392 cell2424414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2424545536 cell2424676608)
                  (ThetaLowerSegment.join cell2424807680 cell2424938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2425069824 cell2425200896)
                  (ThetaLowerSegment.join cell2425331968 cell2425463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2425594112 cell2425725184)
                  (ThetaLowerSegment.join cell2425856256 cell2425987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2426118400 cell2426249472)
                  (ThetaLowerSegment.join cell2426380544 cell2426511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2426642688 cell2426773760)
                  (ThetaLowerSegment.join cell2426904832 cell2427035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2427166976 cell2427298048)
                  (ThetaLowerSegment.join cell2427429120 cell2427560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2427691264 cell2427822336)
                  (ThetaLowerSegment.join cell2427953408 cell2428084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2428215552 cell2428346624)
                  (ThetaLowerSegment.join cell2428477696 cell2428608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2428739840 cell2428870912)
                  (ThetaLowerSegment.join cell2429001984 cell2429133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2429264128 cell2429395200)
                  (ThetaLowerSegment.join cell2429526272 cell2429657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2429788416 cell2429919488)
                  (ThetaLowerSegment.join cell2430050560 cell2430181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2430312704 cell2430443776)
                  (ThetaLowerSegment.join cell2430574848 cell2430705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2430836992 cell2430968064)
                  (ThetaLowerSegment.join cell2431099136 cell2431230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2431361280 cell2431492352)
                  (ThetaLowerSegment.join cell2431623424 cell2431754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2431885568 cell2432016640)
                  (ThetaLowerSegment.join cell2432147712 cell2432278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2432409856 cell2432540928)
                  (ThetaLowerSegment.join cell2432672000 cell2432803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2432934144 cell2433065216)
                  (ThetaLowerSegment.join cell2433196288 cell2433327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2433458432 cell2433589504)
                  (ThetaLowerSegment.join cell2433720576 cell2433851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2433982720 cell2434113792)
                  (ThetaLowerSegment.join cell2434244864 cell2434375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2434507008 cell2434638080)
                  (ThetaLowerSegment.join cell2434769152 cell2434900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2435031296 cell2435162368)
                  (ThetaLowerSegment.join cell2435293440 cell2435424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2435555584 cell2435686656)
                  (ThetaLowerSegment.join cell2435817728 cell2435948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2436079872 cell2436210944)
                  (ThetaLowerSegment.join cell2436342016 cell2436473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2436604160 cell2436735232)
                  (ThetaLowerSegment.join cell2436866304 cell2436997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2437128448 cell2437259520)
                  (ThetaLowerSegment.join cell2437390592 cell2437521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2437652736 cell2437783808)
                  (ThetaLowerSegment.join cell2437914880 cell2438045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2438177024 cell2438308096)
                  (ThetaLowerSegment.join cell2438439168 cell2438570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2438701312 cell2438832384)
                  (ThetaLowerSegment.join cell2438963456 cell2439094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2439225600 cell2439356672)
                  (ThetaLowerSegment.join cell2439487744 cell2439618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2439749888 cell2439880960)
                  (ThetaLowerSegment.join cell2440012032 cell2440143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2440274176 cell2440405248)
                  (ThetaLowerSegment.join cell2440536320 cell2440667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2440798464 cell2440929536)
                (ThetaLowerSegment.join cell2441060608 cell2441191680))
              (ThetaLowerSegment.join cell2441322752 cell2441339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
