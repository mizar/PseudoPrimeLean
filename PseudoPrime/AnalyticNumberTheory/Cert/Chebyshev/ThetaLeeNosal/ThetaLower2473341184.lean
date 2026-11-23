/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis65536

/-! # Direct theta estimate up to 2473341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell2441341184 :
    ThetaLowerSegment 2441341184 2441472256 (122063898657197 / 50000)
      (122070504445677 / 50000) := by
  exact
    packedTile65536 2441341184 2441472256 14 6112 49409 31 _ _ (108079 / 5000) (2161583 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441472256 :
    ThetaLowerSegment 2441472256 2441603328 (122070504445677 / 50000)
      (244153915715389 / 100000) := by
  exact
    packedTile65536 2441472256 2441603328 14 5971 49411 31 _ _ (432317 / 20000) (540397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441603328 :
    ThetaLowerSegment 2441603328 2441734400 (244153915715389 / 100000) (12208361663877 / 5000) := by
  exact
    packedTile65536 2441603328 2441734400 14 6161 49412 31 _ _ (2161591 / 100000) (1080797 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441734400 :
    ThetaLowerSegment 2441734400 2441865472 (12208361663877 / 5000) (61045089622113 / 25000) := by
  exact
    packedTile65536 2441734400 2441865472 14 6072 49413 31 _ _ (540399 / 25000) (2161599 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441865472 :
    ThetaLowerSegment 2441865472 2441996544 (61045089622113 / 25000) (6104836877083 / 2500) := by
  exact
    packedTile65536 2441865472 2441996544 14 6068 49415 31 _ _ (2161601 / 100000) (540401 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2441996544 :
    ThetaLowerSegment 2441996544 2442127616 (6104836877083 / 2500) (48841308399527 / 20000) := by
  exact
    packedTile65536 2441996544 2442127616 14 6045 49416 31 _ _ (2161607 / 100000) (216161 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442127616 :
    ThetaLowerSegment 2442127616 2442258688 (48841308399527 / 20000)
      (244219675952147 / 100000) := by
  exact
    packedTile65536 2442127616 2442258688 14 6076 49417 31 _ _ (540403 / 25000) (432323 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442258688 :
    ThetaLowerSegment 2442258688 2442389760 (244219675952147 / 100000)
      (244232814260273 / 100000) := by
  exact
    packedTile65536 2442258688 2442389760 14 6078 49419 31 _ _ (2161617 / 100000) (108081 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442389760 :
    ThetaLowerSegment 2442389760 2442520832 (244232814260273 / 100000)
      (122123003322721 / 50000) := by
  exact
    packedTile65536 2442389760 2442520832 14 6103 49420 31 _ _ (2161623 / 100000) (1080813 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442520832 :
    ThetaLowerSegment 2442520832 2442651904 (122123003322721 / 50000)
      (122129495772419 / 50000) := by
  exact
    packedTile65536 2442520832 2442651904 14 6007 49421 31 _ _ (540407 / 25000) (2161631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442651904 :
    ThetaLowerSegment 2442651904 2442782976 (122129495772419 / 50000)
      (122135995805857 / 50000) := by
  exact
    packedTile65536 2442651904 2442782976 14 6014 49423 31 _ _ (1080817 / 50000) (2161637 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442782976 :
    ThetaLowerSegment 2442782976 2442914048 (122135995805857 / 50000)
      (244285210034199 / 100000) := by
  exact
    packedTile65536 2442782976 2442914048 14 6115 49424 31 _ _ (2161639 / 100000) (1080821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2442914048 :
    ThetaLowerSegment 2442914048 2443045120 (244285210034199 / 100000)
      (244298320405059 / 100000) := by
  exact
    packedTile65536 2442914048 2443045120 14 6065 49425 31 _ _ (540411 / 25000) (2161647 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443045120 :
    ThetaLowerSegment 2443045120 2443176192 (244298320405059 / 100000)
      (244311305436609 / 100000) := by
  exact
    packedTile65536 2443045120 2443176192 14 6007 49427 31 _ _ (43233 / 2000) (2161653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443176192 :
    ThetaLowerSegment 2443176192 2443307264 (244311305436609 / 100000)
      (122162153895717 / 50000) := by
  exact
    packedTile65536 2443176192 2443307264 14 6015 49428 31 _ _ (432331 / 20000) (1080829 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443307264 :
    ThetaLowerSegment 2443307264 2443438336 (122162153895717 / 50000)
      (122168708048837 / 50000) := by
  exact
    packedTile65536 2443307264 2443438336 14 6064 49429 31 _ _ (108083 / 5000) (2161663 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443438336 :
    ThetaLowerSegment 2443438336 2443569408 (122168708048837 / 50000)
      (122175270866813 / 50000) := by
  exact
    packedTile65536 2443438336 2443569408 14 6072 49431 31 _ _ (1080833 / 50000) (2161669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443569408 :
    ThetaLowerSegment 2443569408 2443700480 (122175270866813 / 50000) (61090850919019 / 25000) := by
  exact
    packedTile65536 2443569408 2443700480 14 5950 49432 31 _ _ (2161671 / 100000) (1080837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443700480 :
    ThetaLowerSegment 2443700480 2443831552 (61090850919019 / 25000) (7636765934927 / 3125) := by
  exact
    packedTile65536 2443700480 2443831552 14 6063 49433 31 _ _ (540419 / 25000) (2161679 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443831552 :
    ThetaLowerSegment 2443831552 2443962624 (7636765934927 / 3125) (30548709860551 / 12500) := by
  exact
    packedTile65536 2443831552 2443962624 14 6092 49435 31 _ _ (1080841 / 50000) (432337 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2443962624 :
    ThetaLowerSegment 2443962624 2444093696 (30548709860551 / 12500) (122201404485623 / 50000) := by
  exact
    packedTile65536 2443962624 2444093696 14 6074 49436 31 _ _ (2161687 / 100000) (216169 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2444093696 :
    ThetaLowerSegment 2444093696 2444224768 (122201404485623 / 50000)
      (122207915504939 / 50000) := by
  exact
    packedTile65536 2444093696 2444224768 14 6024 49437 31 _ _ (2161693 / 100000) (67553 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2444224768 :
    ThetaLowerSegment 2444224768 2444355840 (122207915504939 / 50000) (4888578790931 / 2000) := by
  exact
    packedTile65536 2444224768 2444355840 14 6064 49439 31 _ _ (1080849 / 50000) (2161701 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2444355840 :
    ThetaLowerSegment 2444355840 2444486912 (4888578790931 / 2000) (244441933543283 / 100000) := by
  exact
    packedTile65536 2444355840 2444486912 14 6011 49440 31 _ _ (2161703 / 100000) (1080853 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2444486912 :
    ThetaLowerSegment 2444486912 2444617984 (244441933543283 / 100000)
      (122227645371597 / 50000) := by
  exact
    packedTile65536 2444486912 2444617984 14 6179 49441 31 _ _ (2161709 / 100000) (135107 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2444617984 :
    ThetaLowerSegment 2444617984 2444749056 (122227645371597 / 50000)
      (122234184556447 / 50000) := by
  exact
    packedTile65536 2444617984 2444749056 14 6050 49443 31 _ _ (1080857 / 50000) (2161717 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2444749056 :
    ThetaLowerSegment 2444749056 2444880128 (122234184556447 / 50000)
      (244481505879257 / 100000) := by
  exact
    packedTile65536 2444749056 2444880128 14 6077 49444 31 _ _ (2161719 / 100000) (1080861 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2444880128 :
    ThetaLowerSegment 2444880128 2445011200 (244481505879257 / 100000) (15280915978277 / 6250) := by
  exact
    packedTile65536 2444880128 2445011200 14 6083 49445 31 _ _ (86469 / 4000) (67554 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445011200 :
    ThetaLowerSegment 2445011200 2445142272 (15280915978277 / 6250) (122253928668771 / 50000) := by
  exact
    packedTile65536 2445011200 2445142272 14 6107 49447 31 _ _ (216173 / 10000) (2161733 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445142272 :
    ThetaLowerSegment 2445142272 2445273344 (122253928668771 / 50000) (61130285840213 / 25000) := by
  exact
    packedTile65536 2445142272 2445273344 14 6146 49448 31 _ _ (432347 / 20000) (1080869 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445273344 :
    ThetaLowerSegment 2445273344 2445404416 (61130285840213 / 25000) (122267067712131 / 50000) := by
  exact
    packedTile65536 2445273344 2445404416 14 6010 49449 31 _ _ (2161741 / 100000) (135109 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445404416 :
    ThetaLowerSegment 2445404416 2445535488 (122267067712131 / 50000)
      (122273708595843 / 50000) := by
  exact
    packedTile65536 2445404416 2445535488 14 6144 49451 31 _ _ (1080873 / 50000) (2161749 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445535488 :
    ThetaLowerSegment 2445535488 2445666560 (122273708595843 / 50000) (61140098005297 / 25000) := by
  exact
    packedTile65536 2445535488 2445666560 14 6002 49452 31 _ _ (2161751 / 100000) (1080877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445666560 :
    ThetaLowerSegment 2445666560 2445797632 (61140098005297 / 25000)
      (244573663047411 / 100000) := by
  exact
    packedTile65536 2445666560 2445797632 14 6139 49453 31 _ _ (2161757 / 100000) (13511 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445797632 :
    ThetaLowerSegment 2445797632 2445928704 (244573663047411 / 100000)
      (244586860604421 / 100000) := by
  exact
    packedTile65536 2445797632 2445928704 14 6105 49455 31 _ _ (1080881 / 50000) (432353 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2445928704 :
    ThetaLowerSegment 2445928704 2446059776 (244586860604421 / 100000)
      (244600006315629 / 100000) := by
  exact
    packedTile65536 2445928704 2446059776 14 6081 49456 31 _ _ (270221 / 12500) (2161771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446059776 :
    ThetaLowerSegment 2446059776 2446190848 (244600006315629 / 100000)
      (122306545763799 / 50000) := by
  exact
    packedTile65536 2446059776 2446190848 14 6053 49457 31 _ _ (2161773 / 100000) (135111 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446190848 :
    ThetaLowerSegment 2446190848 2446321920 (122306545763799 / 50000) (30578261287339 / 12500) := by
  exact
    packedTile65536 2446190848 2446321920 14 6013 49458 31 _ _ (1080889 / 50000) (2161781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446321920 :
    ThetaLowerSegment 2446321920 2446452992 (30578261287339 / 12500) (15289949554471 / 6250) := by
  exact
    packedTile65536 2446321920 2446452992 14 6061 49460 31 _ _ (270223 / 12500) (2161787 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446452992 :
    ThetaLowerSegment 2446452992 2446584064 (15289949554471 / 6250) (30581544230371 / 12500) := by
  exact
    packedTile65536 2446452992 2446584064 14 6088 49461 31 _ _ (2161789 / 100000) (67556 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446584064 :
    ThetaLowerSegment 2446584064 2446715136 (30581544230371 / 12500) (122332728238201 / 50000) := by
  exact
    packedTile65536 2446584064 2446715136 14 6061 49462 31 _ _ (1080897 / 50000) (2161797 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446715136 :
    ThetaLowerSegment 2446715136 2446846208 (122332728238201 / 50000)
      (122339237418001 / 50000) := by
  exact
    packedTile65536 2446715136 2446846208 14 6022 49464 31 _ _ (10809 / 500) (2161803 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446846208 :
    ThetaLowerSegment 2446846208 2446977280 (122339237418001 / 50000)
      (244691638066647 / 100000) := by
  exact
    packedTile65536 2446846208 2446977280 14 6089 49465 31 _ _ (432361 / 20000) (135113 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2446977280 :
    ThetaLowerSegment 2446977280 2447108352 (244691638066647 / 100000)
      (244704468408997 / 100000) := by
  exact
    packedTile65536 2446977280 2447108352 14 5935 49466 31 _ _ (216181 / 10000) (2161813 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2447108352 :
    ThetaLowerSegment 2447108352 2447239424 (244704468408997 / 100000)
      (244717577661221 / 100000) := by
  exact
    packedTile65536 2447108352 2447239424 14 6064 49468 31 _ _ (270227 / 12500) (2161819 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2447239424 :
    ThetaLowerSegment 2447239424 2447370496 (244717577661221 / 100000) (97892305043 / 40) := by
  exact
    packedTile65536 2447239424 2447370496 14 6099 49469 31 _ _ (2161821 / 100000) (67557 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2447370496 :
    ThetaLowerSegment 2447370496 2447501568 (97892305043 / 40) (244743887059217 / 100000) := by
  exact
    packedTile65536 2447370496 2447501568 14 6071 49470 31 _ _ (2161827 / 100000) (216183 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2447501568 :
    ThetaLowerSegment 2447501568 2447632640 (244743887059217 / 100000)
      (244757043968769 / 100000) := by
  exact
    packedTile65536 2447501568 2447632640 14 6086 49472 31 _ _ (270229 / 12500) (432367 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2447632640 :
    ThetaLowerSegment 2447632640 2447763712 (244757043968769 / 100000)
      (244770369532037 / 100000) := by
  exact
    packedTile65536 2447632640 2447763712 14 6164 49473 31 _ _ (2161837 / 100000) (27023 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2447763712 :
    ThetaLowerSegment 2447763712 2447894784 (244770369532037 / 100000)
      (244783530832221 / 100000) := by
  exact
    packedTile65536 2447763712 2447894784 14 6088 49474 31 _ _ (2161843 / 100000) (1080923 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2447894784 :
    ThetaLowerSegment 2447894784 2448025856 (244783530832221 / 100000)
      (244796467330653 / 100000) := by
  exact
    packedTile65536 2447894784 2448025856 14 5984 49476 31 _ _ (270231 / 12500) (2161851 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448025856 :
    ThetaLowerSegment 2448025856 2448156928 (244796467330653 / 100000)
      (244809386564181 / 100000) := by
  exact
    packedTile65536 2448025856 2448156928 14 5976 49477 31 _ _ (2161853 / 100000) (67558 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448156928 :
    ThetaLowerSegment 2448156928 2448288000 (244809386564181 / 100000)
      (122411259928803 / 50000) := by
  exact
    packedTile65536 2448156928 2448288000 14 6075 49478 31 _ _ (2161859 / 100000) (1080931 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448288000 :
    ThetaLowerSegment 2448288000 2448419072 (122411259928803 / 50000)
      (122417743358939 / 50000) := by
  exact
    packedTile65536 2448288000 2448419072 14 5998 49480 31 _ _ (270233 / 12500) (2161867 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448419072 :
    ThetaLowerSegment 2448419072 2448550144 (122417743358939 / 50000) (15303035376583 / 6250) := by
  exact
    packedTile65536 2448419072 2448550144 14 6050 49481 31 _ _ (2161869 / 100000) (135117 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448550144 :
    ThetaLowerSegment 2448550144 2448681216 (15303035376583 / 6250) (244861530789703 / 100000) := by
  exact
    packedTile65536 2448550144 2448681216 14 5997 49482 31 _ _ (3459 / 160) (1080939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448681216 :
    ThetaLowerSegment 2448681216 2448812288 (244861530789703 / 100000)
      (244874620973103 / 100000) := by
  exact
    packedTile65536 2448681216 2448812288 14 6055 49484 31 _ _ (54047 / 2500) (2161883 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448812288 :
    ThetaLowerSegment 2448812288 2448943360 (244874620973103 / 100000)
      (244887752262593 / 100000) := by
  exact
    packedTile65536 2448812288 2448943360 14 6074 49485 31 _ _ (432377 / 20000) (67559 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2448943360 :
    ThetaLowerSegment 2448943360 2449074432 (244887752262593 / 100000)
      (122450408284953 / 50000) := by
  exact
    packedTile65536 2448943360 2449074432 14 6043 49486 31 _ _ (2161891 / 100000) (1080947 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449074432 :
    ThetaLowerSegment 2449074432 2449205504 (122450408284953 / 50000)
      (122456962072677 / 50000) := by
  exact
    packedTile65536 2449074432 2449205504 14 6063 49488 31 _ _ (270237 / 12500) (2161899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449205504 :
    ThetaLowerSegment 2449205504 2449336576 (122456962072677 / 50000)
      (122463439128073 / 50000) := by
  exact
    packedTile65536 2449205504 2449336576 14 5992 49489 31 _ _ (2161901 / 100000) (135119 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449336576 :
    ThetaLowerSegment 2449336576 2449467648 (122463439128073 / 50000)
      (244939981574473 / 100000) := by
  exact
    packedTile65536 2449336576 2449467648 14 6061 49490 31 _ _ (2161907 / 100000) (216191 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449467648 :
    ThetaLowerSegment 2449467648 2449598720 (244939981574473 / 100000)
      (244952978989417 / 100000) := by
  exact
    packedTile65536 2449467648 2449598720 14 6012 49492 31 _ _ (270239 / 12500) (432383 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449598720 :
    ThetaLowerSegment 2449598720 2449729792 (244952978989417 / 100000)
      (48993197017621 / 20000) := by
  exact
    packedTile65536 2449598720 2449729792 14 6016 49493 31 _ _ (1080959 / 50000) (2161921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449729792 :
    ThetaLowerSegment 2449729792 2449860864 (48993197017621 / 20000) (30622366605619 / 12500) := by
  exact
    packedTile65536 2449729792 2449860864 14 5989 49494 31 _ _ (2161923 / 100000) (1080963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449860864 :
    ThetaLowerSegment 2449860864 2449991936 (30622366605619 / 12500) (15312001457437 / 6250) := by
  exact
    packedTile65536 2449860864 2449991936 14 6055 49496 31 _ _ (270241 / 12500) (2161931 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2449991936 :
    ThetaLowerSegment 2449991936 2450123008 (15312001457437 / 6250) (30625640579879 / 12500) := by
  exact
    packedTile65536 2449991936 2450123008 14 6060 49497 31 _ _ (1080967 / 50000) (2161937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450123008 :
    ThetaLowerSegment 2450123008 2450254080 (30625640579879 / 12500) (122509102184991 / 50000) := by
  exact
    packedTile65536 2450123008 2450254080 14 6050 49498 31 _ _ (2161939 / 100000) (1080971 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450254080 :
    ThetaLowerSegment 2450254080 2450385152 (122509102184991 / 50000)
      (122515693952247 / 50000) := by
  exact
    packedTile65536 2450254080 2450385152 14 6098 49500 31 _ _ (270243 / 12500) (2161947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450385152 :
    ThetaLowerSegment 2450385152 2450516224 (122515693952247 / 50000)
      (122522194935897 / 50000) := by
  exact
    packedTile65536 2450385152 2450516224 14 6014 49501 31 _ _ (43239 / 2000) (2161953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450516224 :
    ThetaLowerSegment 2450516224 2450647296 (122522194935897 / 50000)
      (245057493481049 / 100000) := by
  exact
    packedTile65536 2450516224 2450647296 14 6061 49502 31 _ _ (432391 / 20000) (1080979 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450647296 :
    ThetaLowerSegment 2450647296 2450778368 (245057493481049 / 100000)
      (245070571177089 / 100000) := by
  exact
    packedTile65536 2450647296 2450778368 14 6049 49504 31 _ _ (54049 / 2500) (2161963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450778368 :
    ThetaLowerSegment 2450778368 2450909440 (245070571177089 / 100000)
      (245083530001293 / 100000) := by
  exact
    packedTile65536 2450778368 2450909440 14 5994 49505 31 _ _ (1080983 / 50000) (2161969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2450909440 :
    ThetaLowerSegment 2450909440 2451040512 (245083530001293 / 100000)
      (245096583982191 / 100000) := by
  exact
    packedTile65536 2450909440 2451040512 14 6038 49506 31 _ _ (2161971 / 100000) (1080987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451040512 :
    ThetaLowerSegment 2451040512 2451171584 (245096583982191 / 100000)
      (245109852028903 / 100000) := by
  exact
    packedTile65536 2451040512 2451171584 14 6137 49507 31 _ _ (270247 / 12500) (2161979 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451171584 :
    ThetaLowerSegment 2451171584 2451302656 (245109852028903 / 100000)
      (245122983907571 / 100000) := by
  exact
    packedTile65536 2451171584 2451302656 14 6074 49509 31 _ _ (1080991 / 50000) (432397 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451302656 :
    ThetaLowerSegment 2451302656 2451433728 (245122983907571 / 100000)
      (245136159056349 / 100000) := by
  exact
    packedTile65536 2451302656 2451433728 14 6094 49510 31 _ _ (2161987 / 100000) (216199 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451433728 :
    ThetaLowerSegment 2451433728 2451564800 (245136159056349 / 100000)
      (245149163438229 / 100000) := by
  exact
    packedTile65536 2451433728 2451564800 14 6015 49511 31 _ _ (270249 / 12500) (432399 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451564800 :
    ThetaLowerSegment 2451564800 2451695872 (245149163438229 / 100000)
      (49032466866009 / 20000) := by
  exact
    packedTile65536 2451564800 2451695872 14 6092 49513 31 _ _ (1080999 / 50000) (2162001 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451695872 :
    ThetaLowerSegment 2451695872 2451826944 (49032466866009 / 20000) (24517572793863 / 10000) := by
  exact
    packedTile65536 2451695872 2451826944 14 6195 49514 31 _ _ (2162003 / 100000) (1081003 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451826944 :
    ThetaLowerSegment 2451826944 2451958016 (24517572793863 / 10000) (122594454850703 / 50000) := by
  exact
    packedTile65536 2451826944 2451958016 14 6097 49515 31 _ _ (270251 / 12500) (2162011 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2451958016 :
    ThetaLowerSegment 2451958016 2452089088 (122594454850703 / 50000) (7662556576217 / 3125) := by
  exact
    packedTile65536 2451958016 2452089088 14 5967 49517 31 _ _ (1081007 / 50000) (2162017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2452089088 :
    ThetaLowerSegment 2452089088 2452220160 (7662556576217 / 3125) (122607466947137 / 50000) := by
  exact
    packedTile65536 2452089088 2452220160 14 6070 49518 31 _ _ (2162019 / 100000) (1081011 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2452220160 :
    ThetaLowerSegment 2452220160 2452351232 (122607466947137 / 50000)
      (122613987611521 / 50000) := by
  exact
    packedTile65536 2452220160 2452351232 14 6032 49519 31 _ _ (270253 / 12500) (2162027 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2452351232 :
    ThetaLowerSegment 2452351232 2452482304 (122613987611521 / 50000)
      (122620616395501 / 50000) := by
  exact
    packedTile65536 2452351232 2452482304 14 6132 49521 31 _ _ (216203 / 10000) (2162033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2452482304 :
    ThetaLowerSegment 2452482304 2452613376 (122620616395501 / 50000)
      (122627301407721 / 50000) := by
  exact
    packedTile65536 2452482304 2452613376 14 6184 49522 31 _ _ (432407 / 20000) (1081019 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2452613376 :
    ThetaLowerSegment 2452613376 2452744448 (122627301407721 / 50000)
      (122633864280141 / 50000) := by
  exact
    packedTile65536 2452613376 2452744448 14 6071 49523 31 _ _ (54051 / 2500) (2162043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2452744448 :
    ThetaLowerSegment 2452744448 2452875520 (122633864280141 / 50000) (7665023860488 / 3125) := by
  exact
    packedTile65536 2452744448 2452875520 14 6029 49525 31 _ _ (1081023 / 50000) (2162049 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2452875520 :
    ThetaLowerSegment 2452875520 2453006592 (7665023860488 / 3125) (122647051695143 / 50000) := by
  exact
    packedTile65536 2452875520 2453006592 14 6170 49526 31 _ _ (2162051 / 100000) (1081027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453006592 :
    ThetaLowerSegment 2453006592 2453137664 (122647051695143 / 50000) (49061444118021 / 20000) := by
  exact
    packedTile65536 2453006592 2453137664 14 6067 49527 31 _ _ (2162057 / 100000) (108103 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453137664 :
    ThetaLowerSegment 2453137664 2453268736 (49061444118021 / 20000) (49064034268297 / 20000) := by
  exact
    packedTile65536 2453137664 2453268736 14 5990 49529 31 _ _ (1081031 / 50000) (432413 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453268736 :
    ThetaLowerSegment 2453268736 2453399808 (49064034268297 / 20000) (61333292962589 / 25000) := by
  exact
    packedTile65536 2453268736 2453399808 14 6013 49530 31 _ _ (2162067 / 100000) (216207 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453399808 :
    ThetaLowerSegment 2453399808 2453530880 (61333292962589 / 25000) (24534626968859 / 10000) := by
  exact
    packedTile65536 2453399808 2453530880 14 6058 49531 31 _ _ (2162073 / 100000) (540519 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453530880 :
    ThetaLowerSegment 2453530880 2453661952 (24534626968859 / 10000) (30669919052821 / 12500) := by
  exact
    packedTile65536 2453530880 2453661952 14 6051 49533 31 _ _ (1081039 / 50000) (2162081 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453661952 :
    ThetaLowerSegment 2453661952 2453793024 (30669919052821 / 12500) (122686277050683 / 50000) := by
  exact
    packedTile65536 2453661952 2453793024 14 6106 49534 31 _ _ (2162083 / 100000) (1081043 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453793024 :
    ThetaLowerSegment 2453793024 2453924096 (122686277050683 / 50000) (6134641733331 / 2500) := by
  exact
    packedTile65536 2453793024 2453924096 14 6066 49535 31 _ _ (2162089 / 100000) (540523 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2453924096 :
    ThetaLowerSegment 2453924096 2454055168 (6134641733331 / 2500) (122699328515949 / 50000) := by
  exact
    packedTile65536 2453924096 2454055168 14 6007 49537 31 _ _ (1081047 / 50000) (2162097 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454055168 :
    ThetaLowerSegment 2454055168 2454186240 (122699328515949 / 50000)
      (245411540979839 / 100000) := by
  exact
    packedTile65536 2454055168 2454186240 14 5959 49538 31 _ _ (2162099 / 100000) (1081051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454186240 :
    ThetaLowerSegment 2454186240 2454317312 (245411540979839 / 100000)
      (122712320587017 / 50000) := by
  exact
    packedTile65536 2454186240 2454317312 14 6059 49539 31 _ _ (432421 / 20000) (540527 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454317312 :
    ThetaLowerSegment 2454317312 2454448384 (122712320587017 / 50000)
      (122718902049857 / 50000) := by
  exact
    packedTile65536 2454317312 2454448384 14 6088 49541 31 _ _ (216211 / 10000) (2162113 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454448384 :
    ThetaLowerSegment 2454448384 2454579456 (122718902049857 / 50000)
      (245450938948339 / 100000) := by
  exact
    packedTile65536 2454448384 2454579456 14 6075 49542 31 _ _ (432423 / 20000) (1081059 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454579456 :
    ThetaLowerSegment 2454579456 2454710528 (245450938948339 / 100000)
      (245463980862211 / 100000) := by
  exact
    packedTile65536 2454579456 2454710528 14 6032 49543 31 _ _ (2162121 / 100000) (540531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454710528 :
    ThetaLowerSegment 2454710528 2454841600 (245463980862211 / 100000) (9819085841897 / 4000) := by
  exact
    packedTile65536 2454710528 2454841600 14 6089 49545 31 _ _ (1081063 / 50000) (2162129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454841600 :
    ThetaLowerSegment 2454841600 2454972672 (9819085841897 / 4000) (245490283155381 / 100000) := by
  exact
    packedTile65536 2454841600 2454972672 14 6076 49546 31 _ _ (2162131 / 100000) (1081067 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2454972672 :
    ThetaLowerSegment 2454972672 2455103744 (245490283155381 / 100000) (2455034440833 / 1000) := by
  exact
    packedTile65536 2454972672 2455103744 14 6087 49547 31 _ _ (2162137 / 100000) (108107 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2455103744 :
    ThetaLowerSegment 2455103744 2455234816 (2455034440833 / 1000) (122758369547229 / 50000) := by
  exact
    packedTile65536 2455103744 2455234816 14 6149 49549 31 _ _ (1081071 / 50000) (432429 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2455234816 :
    ThetaLowerSegment 2455234816 2455365888 (122758369547229 / 50000) (9821198078991 / 4000) := by
  exact
    packedTile65536 2455234816 2455365888 14 6111 49550 31 _ _ (2162147 / 100000) (43243 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2455365888 :
    ThetaLowerSegment 2455365888 2455496960 (9821198078991 / 4000) (245543084892097 / 100000) := by
  exact
    packedTile65536 2455365888 2455496960 14 6074 49551 31 _ _ (2162153 / 100000) (540539 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2455496960 :
    ThetaLowerSegment 2455496960 2455628032 (245543084892097 / 100000)
      (245556120542679 / 100000) := by
  exact
    packedTile65536 2455496960 2455628032 14 6029 49552 31 _ _ (1081079 / 50000) (2162161 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2455628032 :
    ThetaLowerSegment 2455628032 2455759104 (245556120542679 / 100000) (7674040861713 / 3125) := by
  exact
    packedTile65536 2455628032 2455759104 14 6099 49554 31 _ _ (2162163 / 100000) (1081083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2455759104 :
    ThetaLowerSegment 2455759104 2455890176 (7674040861713 / 3125) (245582451400167 / 100000) := by
  exact
    packedTile65536 2455759104 2455890176 14 6079 49555 31 _ _ (2162169 / 100000) (540543 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2455890176 :
    ThetaLowerSegment 2455890176 2456021248 (245582451400167 / 100000)
      (245595606066783 / 100000) := by
  exact
    packedTile65536 2455890176 2456021248 14 6084 49556 31 _ _ (1081087 / 50000) (2162177 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456021248 :
    ThetaLowerSegment 2456021248 2456152320 (245595606066783 / 100000)
      (245608804007399 / 100000) := by
  exact
    packedTile65536 2456021248 2456152320 14 6104 49558 31 _ _ (2162179 / 100000) (1081091 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456152320 :
    ThetaLowerSegment 2456152320 2456283392 (245608804007399 / 100000) (7675680602487 / 3125) := by
  exact
    packedTile65536 2456152320 2456283392 14 6001 49559 31 _ _ (432437 / 20000) (540547 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456283392 :
    ThetaLowerSegment 2456283392 2456414464 (7675680602487 / 3125) (61408730267601 / 25000) := by
  exact
    packedTile65536 2456283392 2456414464 14 6078 49560 31 _ _ (216219 / 10000) (2162193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456414464 :
    ThetaLowerSegment 2456414464 2456545536 (61408730267601 / 25000)
      (245648004512349 / 100000) := by
  exact
    packedTile65536 2456414464 2456545536 14 6051 49562 31 _ _ (432439 / 20000) (1081099 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456545536 :
    ThetaLowerSegment 2456545536 2456676608 (245648004512349 / 100000)
      (245660977718349 / 100000) := by
  exact
    packedTile65536 2456545536 2456676608 14 6000 49563 31 _ _ (2162201 / 100000) (540551 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456676608 :
    ThetaLowerSegment 2456676608 2456807680 (245660977718349 / 100000)
      (245674002847293 / 100000) := by
  exact
    packedTile65536 2456676608 2456807680 14 6024 49564 31 _ _ (1081103 / 50000) (2162209 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456807680 :
    ThetaLowerSegment 2456807680 2456938752 (245674002847293 / 100000)
      (122843621032623 / 50000) := by
  exact
    packedTile65536 2456807680 2456938752 14 6123 49566 31 _ _ (2162211 / 100000) (1081107 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2456938752 :
    ThetaLowerSegment 2456938752 2457069824 (122843621032623 / 50000)
      (122850241741077 / 50000) := by
  exact
    packedTile65536 2456938752 2457069824 14 6124 49567 31 _ _ (2162217 / 100000) (108111 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457069824 :
    ThetaLowerSegment 2457069824 2457200896 (122850241741077 / 50000) (61428372311871 / 25000) := by
  exact
    packedTile65536 2457069824 2457200896 14 6015 49568 31 _ _ (1081111 / 50000) (86489 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457200896 :
    ThetaLowerSegment 2457200896 2457331968 (61428372311871 / 25000) (12286332644273 / 5000) := by
  exact
    packedTile65536 2457200896 2457331968 14 6088 49570 31 _ _ (2162227 / 100000) (216223 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457331968 :
    ThetaLowerSegment 2457331968 2457463040 (12286332644273 / 5000) (49147910121061 / 20000) := by
  exact
    packedTile65536 2457331968 2457463040 14 5965 49571 31 _ _ (2162233 / 100000) (540559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457463040 :
    ThetaLowerSegment 2457463040 2457594112 (49147910121061 / 20000)
      (245752850531243 / 100000) := by
  exact
    packedTile65536 2457463040 2457594112 14 6151 49572 31 _ _ (1081119 / 50000) (2162241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457594112 :
    ThetaLowerSegment 2457594112 2457725184 (245752850531243 / 100000)
      (49153192474559 / 20000) := by
  exact
    packedTile65536 2457594112 2457725184 14 6064 49574 31 _ _ (2162243 / 100000) (1081123 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457725184 :
    ThetaLowerSegment 2457725184 2457856256 (49153192474559 / 20000) (61444721533767 / 25000) := by
  exact
    packedTile65536 2457725184 2457856256 14 5977 49575 31 _ _ (2162249 / 100000) (540563 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457856256 :
    ThetaLowerSegment 2457856256 2457987328 (61444721533767 / 25000) (122896032536599 / 50000) := by
  exact
    packedTile65536 2457856256 2457987328 14 6095 49576 31 _ _ (1081127 / 50000) (2162257 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2457987328 :
    ThetaLowerSegment 2457987328 2458118400 (122896032536599 / 50000) (61451282360519 / 25000) := by
  exact
    packedTile65536 2457987328 2458118400 14 6042 49578 31 _ _ (2162259 / 100000) (1081131 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458118400 :
    ThetaLowerSegment 2458118400 2458249472 (61451282360519 / 25000) (122909187738733 / 50000) := by
  exact
    packedTile65536 2458118400 2458249472 14 6126 49579 31 _ _ (432453 / 20000) (540567 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458249472 :
    ThetaLowerSegment 2458249472 2458380544 (122909187738733 / 50000)
      (122915696171433 / 50000) := by
  exact
    packedTile65536 2458249472 2458380544 14 6020 49580 31 _ _ (216227 / 10000) (2162273 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458380544 :
    ThetaLowerSegment 2458380544 2458511616 (122915696171433 / 50000)
      (245844307611441 / 100000) := by
  exact
    packedTile65536 2458380544 2458511616 14 5973 49582 31 _ _ (86491 / 4000) (1081139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458511616 :
    ThetaLowerSegment 2458511616 2458642688 (245844307611441 / 100000)
      (122928723896539 / 50000) := by
  exact
    packedTile65536 2458511616 2458642688 14 6077 49583 31 _ _ (2162281 / 100000) (540571 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458642688 :
    ThetaLowerSegment 2458642688 2458773760 (122928723896539 / 50000)
      (122935336167127 / 50000) := by
  exact
    packedTile65536 2458642688 2458773760 14 6116 49584 31 _ _ (1081143 / 50000) (2162289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458773760 :
    ThetaLowerSegment 2458773760 2458904832 (122935336167127 / 50000)
      (122941913856349 / 50000) := by
  exact
    packedTile65536 2458773760 2458904832 14 6084 49586 31 _ _ (2162291 / 100000) (1081147 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2458904832 :
    ThetaLowerSegment 2458904832 2459035904 (122941913856349 / 50000) (61474249025357 / 25000) := by
  exact
    packedTile65536 2458904832 2459035904 14 6090 49587 31 _ _ (2162297 / 100000) (21623 / 1000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459035904 :
    ThetaLowerSegment 2459035904 2459166976 (61474249025357 / 25000) (24591012343687 / 10000) := by
  exact
    packedTile65536 2459035904 2459166976 14 6071 49588 31 _ _ (1081151 / 50000) (432461 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459166976 :
    ThetaLowerSegment 2459166976 2459298048 (24591012343687 / 10000) (49184634591923 / 20000) := by
  exact
    packedTile65536 2459166976 2459298048 14 6035 49589 31 _ _ (2162307 / 100000) (216231 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459298048 :
    ThetaLowerSegment 2459298048 2459429120 (49184634591923 / 20000)
      (245936194408501 / 100000) := by
  exact
    packedTile65536 2459298048 2459429120 14 6022 49591 31 _ _ (2162313 / 100000) (540579 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459429120 :
    ThetaLowerSegment 2459429120 2459560192 (245936194408501 / 100000)
      (245949382385983 / 100000) := by
  exact
    packedTile65536 2459429120 2459560192 14 6099 49592 31 _ _ (1081159 / 50000) (2162321 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459560192 :
    ThetaLowerSegment 2459560192 2459691264 (245949382385983 / 100000)
      (122981213840321 / 50000) := by
  exact
    packedTile65536 2459560192 2459691264 14 6033 49593 31 _ _ (2162323 / 100000) (1081163 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459691264 :
    ThetaLowerSegment 2459691264 2459822336 (122981213840321 / 50000) (61493877442773 / 25000) := by
  exact
    packedTile65536 2459691264 2459822336 14 6050 49595 31 _ _ (2162329 / 100000) (540583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459822336 :
    ThetaLowerSegment 2459822336 2459953408 (61493877442773 / 25000) (12299423323821 / 5000) := by
  exact
    packedTile65536 2459822336 2459953408 14 5992 49596 31 _ _ (1081167 / 50000) (2162337 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2459953408 :
    ThetaLowerSegment 2459953408 2460084480 (12299423323821 / 5000) (123000761339651 / 50000) := by
  exact
    packedTile65536 2459953408 2460084480 14 6038 49597 31 _ _ (2162339 / 100000) (1081171 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2460084480 :
    ThetaLowerSegment 2460084480 2460215552 (123000761339651 / 50000) (61503657703673 / 25000) := by
  exact
    packedTile65536 2460084480 2460215552 14 6062 49599 31 _ _ (432469 / 20000) (540587 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2460215552 :
    ThetaLowerSegment 2460215552 2460346624 (61503657703673 / 25000) (123013853272571 / 50000) := by
  exact
    packedTile65536 2460215552 2460346624 14 6047 49600 31 _ _ (43247 / 2000) (2162353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2460346624 :
    ThetaLowerSegment 2460346624 2460477696 (123013853272571 / 50000) (61510214497063 / 25000) := by
  exact
    packedTile65536 2460346624 2460477696 14 6082 49601 31 _ _ (432471 / 20000) (1081179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2460477696 :
    ThetaLowerSegment 2460477696 2460608768 (61510214497063 / 25000) (123027004733927 / 50000) := by
  exact
    packedTile65536 2460477696 2460608768 14 6082 49603 31 _ _ (2162361 / 100000) (540591 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2460608768 :
    ThetaLowerSegment 2460608768 2460739840 (123027004733927 / 50000)
      (123033545891077 / 50000) := by
  exact
    packedTile65536 2460608768 2460739840 14 6050 49604 31 _ _ (1081183 / 50000) (2162369 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2460739840 :
    ThetaLowerSegment 2460739840 2460870912 (123033545891077 / 50000) (61520054343531 / 25000) := by
  exact
    packedTile65536 2460739840 2460870912 14 6070 49605 31 _ _ (2162371 / 100000) (1081187 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2460870912 :
    ThetaLowerSegment 2460870912 2461001984 (61520054343531 / 25000)
      (246093483557019 / 100000) := by
  exact
    packedTile65536 2460870912 2461001984 14 6135 49607 31 _ _ (2162377 / 100000) (108119 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461001984 :
    ThetaLowerSegment 2461001984 2461133056 (246093483557019 / 100000)
      (246106639489107 / 100000) := by
  exact
    packedTile65536 2461001984 2461133056 14 6084 49608 31 _ _ (1081191 / 50000) (432477 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461133056 :
    ThetaLowerSegment 2461133056 2461264128 (246106639489107 / 100000)
      (123059842584939 / 50000) := by
  exact
    packedTile65536 2461133056 2461264128 14 6033 49609 31 _ _ (2162387 / 100000) (216239 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461264128 :
    ThetaLowerSegment 2461264128 2461395200 (123059842584939 / 50000) (1230662800289 / 500) := by
  exact
    packedTile65536 2461264128 2461395200 14 5954 49611 31 _ _ (2162393 / 100000) (540599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461395200 :
    ThetaLowerSegment 2461395200 2461526272 (1230662800289 / 500) (123072861287213 / 50000) := by
  exact
    packedTile65536 2461395200 2461526272 14 6087 49612 31 _ _ (1081199 / 50000) (2162401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461526272 :
    ThetaLowerSegment 2461526272 2461657344 (123072861287213 / 50000) (7692462659768 / 3125) := by
  exact
    packedTile65536 2461526272 2461657344 14 6050 49613 31 _ _ (2162403 / 100000) (1081203 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461657344 :
    ThetaLowerSegment 2461657344 2461788416 (7692462659768 / 3125) (246171842276437 / 100000) := by
  exact
    packedTile65536 2461657344 2461788416 14 6029 49615 31 _ _ (2162409 / 100000) (540603 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461788416 :
    ThetaLowerSegment 2461788416 2461919488 (246171842276437 / 100000)
      (246185007052869 / 100000) := by
  exact
    packedTile65536 2461788416 2461919488 14 6088 49616 31 _ _ (1081207 / 50000) (2162417 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2461919488 :
    ThetaLowerSegment 2461919488 2462050560 (246185007052869 / 100000)
      (246198024815249 / 100000) := by
  exact
    packedTile65536 2461919488 2462050560 14 6020 49617 31 _ _ (2162419 / 100000) (1081211 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462050560 :
    ThetaLowerSegment 2462050560 2462181632 (246198024815249 / 100000)
      (123105604560237 / 50000) := by
  exact
    packedTile65536 2462050560 2462181632 14 6097 49619 31 _ _ (86497 / 4000) (540607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462181632 :
    ThetaLowerSegment 2462181632 2462312704 (123105604560237 / 50000)
      (123112128611547 / 50000) := by
  exact
    packedTile65536 2462181632 2462312704 14 6034 49620 31 _ _ (216243 / 10000) (2162433 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462312704 :
    ThetaLowerSegment 2462312704 2462443776 (123112128611547 / 50000)
      (246237164797609 / 100000) := by
  exact
    packedTile65536 2462312704 2462443776 14 5969 49621 31 _ _ (432487 / 20000) (1081219 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462443776 :
    ThetaLowerSegment 2462443776 2462574848 (246237164797609 / 100000)
      (246250256215423 / 100000) := by
  exact
    packedTile65536 2462443776 2462574848 14 6054 49623 31 _ _ (2162441 / 100000) (540611 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462574848 :
    ThetaLowerSegment 2462574848 2462705920 (246250256215423 / 100000)
      (246263107632001 / 100000) := by
  exact
    packedTile65536 2462574848 2462705920 14 5943 49624 31 _ _ (1081223 / 50000) (2162449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462705920 :
    ThetaLowerSegment 2462705920 2462836992 (246263107632001 / 100000)
      (246276367781533 / 100000) := by
  exact
    packedTile65536 2462705920 2462836992 14 6132 49625 31 _ _ (2162451 / 100000) (1081227 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462836992 :
    ThetaLowerSegment 2462836992 2462968064 (246276367781533 / 100000)
      (246289450640333 / 100000) := by
  exact
    packedTile65536 2462836992 2462968064 14 6050 49626 31 _ _ (270307 / 12500) (2162459 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2462968064 :
    ThetaLowerSegment 2462968064 2463099136 (246289450640333 / 100000)
      (246302364863397 / 100000) := by
  exact
    packedTile65536 2462968064 2463099136 14 5972 49628 31 _ _ (1081231 / 50000) (432493 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2463099136 :
    ThetaLowerSegment 2463099136 2463230208 (246302364863397 / 100000) (2463155753743 / 1000) := by
  exact
    packedTile65536 2463099136 2463230208 14 6109 49629 31 _ _ (2162467 / 100000) (216247 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2463230208 :
    ThetaLowerSegment 2463230208 2463361280 (2463155753743 / 1000) (61582193235229 / 25000) := by
  exact
    packedTile65536 2463230208 2463361280 14 6103 49630 31 _ _ (270309 / 12500) (86499 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2463361280 :
    ThetaLowerSegment 2463361280 2463492352 (61582193235229 / 25000) (123170879310653 / 50000) := by
  exact
    packedTile65536 2463361280 2463492352 14 6005 49632 31 _ _ (1081239 / 50000) (2162481 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2463492352 :
    ThetaLowerSegment 2463492352 2463623424 (123170879310653 / 50000)
      (246354813531177 / 100000) := by
  exact
    packedTile65536 2463492352 2463623424 14 6037 49633 31 _ _ (2162483 / 100000) (1081243 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2463623424 :
    ThetaLowerSegment 2463623424 2463754496 (246354813531177 / 100000)
      (246367818734009 / 100000) := by
  exact
    packedTile65536 2463623424 2463754496 14 6014 49634 31 _ _ (270311 / 12500) (2162491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2463754496 :
    ThetaLowerSegment 2463754496 2463885568 (246367818734009 / 100000)
      (246381068334747 / 100000) := by
  exact
    packedTile65536 2463754496 2463885568 14 6127 49636 31 _ _ (1081247 / 50000) (2162497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2463885568 :
    ThetaLowerSegment 2463885568 2464016640 (246381068334747 / 100000)
      (49278835480737 / 20000) := by
  exact
    packedTile65536 2463885568 2464016640 14 6062 49637 31 _ _ (2162499 / 100000) (1081251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464016640 :
    ThetaLowerSegment 2464016640 2464147712 (49278835480737 / 20000)
      (246407057277509 / 100000) := by
  exact
    packedTile65536 2464016640 2464147712 14 5956 49638 31 _ _ (270313 / 12500) (2162507 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464147712 :
    ThetaLowerSegment 2464147712 2464278784 (246407057277509 / 100000)
      (246420196688269 / 100000) := by
  exact
    packedTile65536 2464147712 2464278784 14 6076 49640 31 _ _ (216251 / 10000) (2162513 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464278784 :
    ThetaLowerSegment 2464278784 2464409856 (246420196688269 / 100000)
      (246433301529169 / 100000) := by
  exact
    packedTile65536 2464278784 2464409856 14 6060 49641 31 _ _ (432503 / 20000) (1081259 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464409856 :
    ThetaLowerSegment 2464409856 2464540928 (246433301529169 / 100000)
      (246446527501489 / 100000) := by
  exact
    packedTile65536 2464409856 2464540928 14 6116 49642 31 _ _ (54063 / 2500) (2162523 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464540928 :
    ThetaLowerSegment 2464540928 2464672000 (246446527501489 / 100000)
      (246459586996003 / 100000) := by
  exact
    packedTile65536 2464540928 2464672000 14 6039 49644 31 _ _ (1081263 / 50000) (2162529 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464672000 :
    ThetaLowerSegment 2464672000 2464803072 (246459586996003 / 100000)
      (246472635708057 / 100000) := by
  exact
    packedTile65536 2464672000 2464803072 14 6034 49645 31 _ _ (2162531 / 100000) (1081267 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464803072 :
    ThetaLowerSegment 2464803072 2464934144 (246472635708057 / 100000)
      (246485837990337 / 100000) := by
  exact
    packedTile65536 2464803072 2464934144 14 6105 49646 31 _ _ (270317 / 12500) (2162539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2464934144 :
    ThetaLowerSegment 2464934144 2465065216 (246485837990337 / 100000)
      (246498847843009 / 100000) := by
  exact
    packedTile65536 2464934144 2465065216 14 6016 49648 31 _ _ (1081271 / 50000) (432509 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465065216 :
    ThetaLowerSegment 2465065216 2465196288 (246498847843009 / 100000)
      (123256061859521 / 50000) := by
  exact
    packedTile65536 2465065216 2465196288 14 6139 49649 31 _ _ (2162547 / 100000) (43251 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465196288 :
    ThetaLowerSegment 2465196288 2465327360 (123256061859521 / 50000)
      (123262585197629 / 50000) := by
  exact
    packedTile65536 2465196288 2465327360 14 6033 49650 31 _ _ (270319 / 12500) (432511 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465327360 :
    ThetaLowerSegment 2465327360 2465458432 (123262585197629 / 50000) (61634605097031 / 25000) := by
  exact
    packedTile65536 2465327360 2465458432 14 6127 49652 31 _ _ (1081279 / 50000) (2162561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465458432 :
    ThetaLowerSegment 2465458432 2465589504 (61634605097031 / 25000)
      (246551445505073 / 100000) := by
  exact
    packedTile65536 2465458432 2465589504 14 6023 49653 31 _ _ (2162563 / 100000) (1081283 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465589504 :
    ThetaLowerSegment 2465589504 2465720576 (246551445505073 / 100000)
      (246564544179449 / 100000) := by
  exact
    packedTile65536 2465589504 2465720576 14 6057 49654 31 _ _ (270321 / 12500) (2162571 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465720576 :
    ThetaLowerSegment 2465720576 2465851648 (246564544179449 / 100000)
      (123288830092347 / 50000) := by
  exact
    packedTile65536 2465720576 2465851648 14 6065 49656 31 _ _ (2162573 / 100000) (135161 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465851648 :
    ThetaLowerSegment 2465851648 2465982720 (123288830092347 / 50000)
      (123295412982823 / 50000) := by
  exact
    packedTile65536 2465851648 2465982720 14 6088 49657 31 _ _ (2162579 / 100000) (1081291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2465982720 :
    ThetaLowerSegment 2465982720 2466113792 (123295412982823 / 50000)
      (123302056440871 / 50000) := by
  exact
    packedTile65536 2465982720 2466113792 14 6144 49658 31 _ _ (270323 / 12500) (2162587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466113792 :
    ThetaLowerSegment 2466113792 2466244864 (123302056440871 / 50000) (49323468287731 / 20000) := by
  exact
    packedTile65536 2466113792 2466244864 14 6117 49659 31 _ _ (2162589 / 100000) (67581 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466244864 :
    ThetaLowerSegment 2466244864 2466375936 (49323468287731 / 20000) (24663039702467 / 10000) := by
  exact
    packedTile65536 2466244864 2466375936 14 6037 49661 31 _ _ (432519 / 20000) (1081299 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466375936 :
    ThetaLowerSegment 2466375936 2466507008 (24663039702467 / 10000) (24664355644567 / 10000) := by
  exact
    packedTile65536 2466375936 2466507008 14 6085 49662 31 _ _ (10813 / 500) (2162603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466507008 :
    ThetaLowerSegment 2466507008 2466638080 (24664355644567 / 10000) (3083207570053 / 1250) := by
  exact
    packedTile65536 2466507008 2466638080 14 6034 49663 31 _ _ (432521 / 20000) (135163 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466638080 :
    ThetaLowerSegment 2466638080 2466769152 (3083207570053 / 1250) (246669566131963 / 100000) := by
  exact
    packedTile65536 2466638080 2466769152 14 5993 49665 31 _ _ (2162611 / 100000) (1081307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466769152 :
    ThetaLowerSegment 2466769152 2466900224 (246669566131963 / 100000)
      (246682721325091 / 100000) := by
  exact
    packedTile65536 2466769152 2466900224 14 6083 49666 31 _ _ (270327 / 12500) (2162619 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2466900224 :
    ThetaLowerSegment 2466900224 2467031296 (246682721325091 / 100000)
      (246695822483109 / 100000) := by
  exact
    packedTile65536 2466900224 2467031296 14 6058 49667 31 _ _ (2162621 / 100000) (67582 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467031296 :
    ThetaLowerSegment 2467031296 2467162368 (246695822483109 / 100000)
      (246708953954253 / 100000) := by
  exact
    packedTile65536 2467031296 2467162368 14 6072 49669 31 _ _ (2162627 / 100000) (216263 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467162368 :
    ThetaLowerSegment 2467162368 2467293440 (246708953954253 / 100000)
      (246721936234149 / 100000) := by
  exact
    packedTile65536 2467162368 2467293440 14 6003 49670 31 _ _ (270329 / 12500) (432527 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467293440 :
    ThetaLowerSegment 2467293440 2467424512 (246721936234149 / 100000)
      (246735067766013 / 100000) := by
  exact
    packedTile65536 2467293440 2467424512 14 6072 49671 31 _ _ (2162637 / 100000) (27033 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467424512 :
    ThetaLowerSegment 2467424512 2467555584 (246735067766013 / 100000)
      (246748147430877 / 100000) := by
  exact
    packedTile65536 2467424512 2467555584 14 6048 49673 31 _ _ (2162643 / 100000) (1081323 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467555584 :
    ThetaLowerSegment 2467555584 2467686656 (246748147430877 / 100000)
      (246761218475389 / 100000) := by
  exact
    packedTile65536 2467555584 2467686656 14 6044 49674 31 _ _ (270331 / 12500) (2162651 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467686656 :
    ThetaLowerSegment 2467686656 2467817728 (246761218475389 / 100000)
      (24677431766461 / 10000) := by
  exact
    packedTile65536 2467686656 2467817728 14 6057 49675 31 _ _ (2162653 / 100000) (67583 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467817728 :
    ThetaLowerSegment 2467817728 2467948800 (24677431766461 / 10000)
      (246787447167399 / 100000) := by
  exact
    packedTile65536 2467817728 2467948800 14 6071 49677 31 _ _ (2162659 / 100000) (1081331 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2467948800 :
    ThetaLowerSegment 2467948800 2468079872 (246787447167399 / 100000)
      (49360138264347 / 20000) := by
  exact
    packedTile65536 2467948800 2468079872 14 6124 49678 31 _ _ (270333 / 12500) (2162667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468079872 :
    ThetaLowerSegment 2468079872 2468210944 (49360138264347 / 20000) (61703447651967 / 25000) := by
  exact
    packedTile65536 2468079872 2468210944 14 6057 49679 31 _ _ (2162669 / 100000) (135167 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468210944 :
    ThetaLowerSegment 2468210944 2468342016 (61703447651967 / 25000) (123413425498077 / 50000) := by
  exact
    packedTile65536 2468210944 2468342016 14 6039 49681 31 _ _ (1081337 / 50000) (2162677 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468342016 :
    ThetaLowerSegment 2468342016 2468473088 (123413425498077 / 50000)
      (123419983825177 / 50000) := by
  exact
    packedTile65536 2468342016 2468473088 14 6065 49682 31 _ _ (54067 / 2500) (2162683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468473088 :
    ThetaLowerSegment 2468473088 2468604160 (123419983825177 / 50000)
      (246853131913949 / 100000) := by
  exact
    packedTile65536 2468473088 2468604160 14 6087 49683 31 _ _ (432537 / 20000) (67584 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468604160 :
    ThetaLowerSegment 2468604160 2468735232 (246853131913949 / 100000)
      (246866138331609 / 100000) := by
  exact
    packedTile65536 2468604160 2468735232 14 6014 49685 31 _ _ (216269 / 10000) (2162693 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468735232 :
    ThetaLowerSegment 2468735232 2468866304 (246866138331609 / 100000)
      (246879250757457 / 100000) := by
  exact
    packedTile65536 2468735232 2468866304 14 6063 49686 31 _ _ (270337 / 12500) (2162699 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468866304 :
    ThetaLowerSegment 2468866304 2468997376 (246879250757457 / 100000)
      (123446162142501 / 50000) := by
  exact
    packedTile65536 2468866304 2468997376 14 6045 49687 31 _ _ (2162701 / 100000) (135169 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2468997376 :
    ThetaLowerSegment 2468997376 2469128448 (123446162142501 / 50000) (12345262106397 / 5000) := by
  exact
    packedTile65536 2468997376 2469128448 14 5973 49689 31 _ _ (1081353 / 50000) (2162709 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2469128448 :
    ThetaLowerSegment 2469128448 2469259520 (12345262106397 / 5000) (12345918489489 / 5000) := by
  exact
    packedTile65536 2469128448 2469259520 14 6070 49690 31 _ _ (270339 / 12500) (432543 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2469259520 :
    ThetaLowerSegment 2469259520 2469390592 (12345918489489 / 5000) (123465696835777 / 50000) := by
  exact
    packedTile65536 2469259520 2469390592 14 6022 49691 31 _ _ (2162717 / 100000) (13517 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2469390592 :
    ThetaLowerSegment 2469390592 2469521664 (123465696835777 / 50000) (61736097367013 / 25000) := by
  exact
    packedTile65536 2469390592 2469521664 14 6009 49692 31 _ _ (1081361 / 50000) (86509 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2469521664 :
    ThetaLowerSegment 2469521664 2469652736 (61736097367013 / 25000) (12347894893357 / 5000) := by
  exact
    packedTile65536 2469521664 2469652736 14 6246 49694 31 _ _ (270341 / 12500) (2162731 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2469652736 :
    ThetaLowerSegment 2469652736 2469783808 (12347894893357 / 5000) (246971218139687 / 100000) := by
  exact
    packedTile65536 2469652736 2469783808 14 6159 49695 31 _ _ (2162733 / 100000) (135171 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2469783808 :
    ThetaLowerSegment 2469783808 2469914880 (246971218139687 / 100000)
      (246984252961613 / 100000) := by
  exact
    packedTile65536 2469783808 2469914880 14 6027 49696 31 _ _ (1081369 / 50000) (2162741 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2469914880 :
    ThetaLowerSegment 2469914880 2470045952 (246984252961613 / 100000)
      (246997398113567 / 100000) := by
  exact
    packedTile65536 2469914880 2470045952 14 6078 49698 31 _ _ (2162743 / 100000) (1081373 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470045952 :
    ThetaLowerSegment 2470045952 2470177024 (246997398113567 / 100000)
      (247010469768523 / 100000) := by
  exact
    packedTile65536 2470045952 2470177024 14 6044 49699 31 _ _ (2162749 / 100000) (67586 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470177024 :
    ThetaLowerSegment 2470177024 2470308096 (247010469768523 / 100000)
      (247023567406747 / 100000) := by
  exact
    packedTile65536 2470177024 2470308096 14 6056 49700 31 _ _ (1081377 / 50000) (2162757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470308096 :
    ThetaLowerSegment 2470308096 2470439168 (247023567406747 / 100000)
      (247036781864237 / 100000) := by
  exact
    packedTile65536 2470308096 2470439168 14 6110 49702 31 _ _ (2162759 / 100000) (1081381 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470439168 :
    ThetaLowerSegment 2470439168 2470570240 (247036781864237 / 100000)
      (247049862266957 / 100000) := by
  exact
    packedTile65536 2470439168 2470570240 14 6048 49703 31 _ _ (432553 / 20000) (135173 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470570240 :
    ThetaLowerSegment 2470570240 2470701312 (247049862266957 / 100000)
      (247063016234097 / 100000) := by
  exact
    packedTile65536 2470570240 2470701312 14 6082 49704 31 _ _ (216277 / 10000) (2162773 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470701312 :
    ThetaLowerSegment 2470701312 2470832384 (247063016234097 / 100000)
      (123538086197211 / 50000) := by
  exact
    packedTile65536 2470701312 2470832384 14 6083 49706 31 _ _ (86511 / 4000) (1081389 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470832384 :
    ThetaLowerSegment 2470832384 2470963456 (123538086197211 / 50000) (61772325118773 / 25000) := by
  exact
    packedTile65536 2470832384 2470963456 14 6070 49707 31 _ _ (2162781 / 100000) (67587 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2470963456 :
    ThetaLowerSegment 2470963456 2471094528 (61772325118773 / 25000) (61775597413991 / 25000) := by
  exact
    packedTile65536 2470963456 2471094528 14 6052 49708 31 _ _ (1081393 / 50000) (2162789 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471094528 :
    ThetaLowerSegment 2471094528 2471225600 (61775597413991 / 25000)
      (247115381541501 / 100000) := by
  exact
    packedTile65536 2471094528 2471225600 14 6007 49710 31 _ _ (2162791 / 100000) (1081397 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471225600 :
    ThetaLowerSegment 2471225600 2471356672 (247115381541501 / 100000)
      (247128587579983 / 100000) := by
  exact
    packedTile65536 2471225600 2471356672 14 6106 49711 31 _ _ (2162797 / 100000) (5407 / 250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471356672 :
    ThetaLowerSegment 2471356672 2471487744 (247128587579983 / 100000)
      (247141629276043 / 100000) := by
  exact
    packedTile65536 2471356672 2471487744 14 6030 49712 31 _ _ (1081401 / 50000) (432561 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471487744 :
    ThetaLowerSegment 2471487744 2471618816 (247141629276043 / 100000) (7723585969566 / 3125) := by
  exact
    packedTile65536 2471487744 2471618816 14 6067 49714 31 _ _ (2162807 / 100000) (216281 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471618816 :
    ThetaLowerSegment 2471618816 2471749888 (7723585969566 / 3125) (61791928189607 / 25000) := by
  exact
    packedTile65536 2471618816 2471749888 14 5993 49715 31 _ _ (540703 / 25000) (432563 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471749888 :
    ThetaLowerSegment 2471749888 2471880960 (61791928189607 / 25000) (30897605132961 / 12500) := by
  exact
    packedTile65536 2471749888 2471880960 14 6070 49716 31 _ _ (1081409 / 50000) (2162821 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2471880960 :
    ThetaLowerSegment 2471880960 2472012032 (30897605132961 / 12500) (123596893861083 / 50000) := by
  exact
    packedTile65536 2471880960 2472012032 14 5986 49718 31 _ _ (2162823 / 100000) (1081413 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472012032 :
    ThetaLowerSegment 2472012032 2472143104 (123596893861083 / 50000)
      (123603468858203 / 50000) := by
  exact
    packedTile65536 2472012032 2472143104 14 6080 49719 31 _ _ (540707 / 25000) (2162831 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472143104 :
    ThetaLowerSegment 2472143104 2472274176 (123603468858203 / 50000) (61805012744737 / 25000) := by
  exact
    packedTile65536 2472143104 2472274176 14 6063 49720 31 _ _ (1081417 / 50000) (2162837 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472274176 :
    ThetaLowerSegment 2472274176 2472405248 (61805012744737 / 25000)
      (247233371904349 / 100000) := by
  exact
    packedTile65536 2472274176 2472405248 14 6159 49721 31 _ _ (2162839 / 100000) (1081421 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472405248 :
    ThetaLowerSegment 2472405248 2472536320 (247233371904349 / 100000)
      (247246658255041 / 100000) := by
  exact
    packedTile65536 2472405248 2472536320 14 6143 49723 31 _ _ (540711 / 25000) (2162847 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472536320 :
    ThetaLowerSegment 2472536320 2472667392 (247246658255041 / 100000)
      (247259713217641 / 100000) := by
  exact
    packedTile65536 2472536320 2472667392 14 6036 49724 31 _ _ (43257 / 2000) (2162853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472667392 :
    ThetaLowerSegment 2472667392 2472798464 (247259713217641 / 100000)
      (247272980170211 / 100000) := by
  exact
    packedTile65536 2472667392 2472798464 14 6134 49725 31 _ _ (432571 / 20000) (1081429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472798464 :
    ThetaLowerSegment 2472798464 2472929536 (247272980170211 / 100000)
      (247286074124651 / 100000) := by
  exact
    packedTile65536 2472798464 2472929536 14 6054 49727 31 _ _ (108143 / 5000) (2162863 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2472929536 :
    ThetaLowerSegment 2472929536 2473060608 (247286074124651 / 100000)
      (247299250298231 / 100000) := by
  exact
    packedTile65536 2472929536 2473060608 14 6092 49728 31 _ _ (432573 / 20000) (540717 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473060608 :
    ThetaLowerSegment 2473060608 2473191680 (247299250298231 / 100000) (15457031388053 / 6250) := by
  exact
    packedTile65536 2473060608 2473191680 14 6127 49729 31 _ _ (2162871 / 100000) (1081437 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473191680 :
    ThetaLowerSegment 2473191680 2473322752 (15457031388053 / 6250) (61831410420137 / 25000) := by
  exact
    packedTile65536 2473191680 2473322752 14 6075 49731 31 _ _ (540719 / 25000) (2162879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473322752 :
    ThetaLowerSegment 2473322752 2473339136 (61831410420137 / 25000) (123663640572173 / 50000) := by
  exact
    packedTile65536 2473322752 2473339136 11 758 49732 31 _ _ (2162881 / 100000) (540721 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell2473339136 :
    ThetaLowerSegment 2473339136 2473341184 (123663640572173 / 50000)
      (123663746553391 / 50000) := by
  exact
    packedTile65536 2473339136 2473341184 8 98 49732 31 _ _ (1081441 / 50000) (432577 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_2441341184_2473341184 :
    ThetaLowerSegment 2441341184 2473341184 (122063898657197 / 50000)
      (123663746553391 / 50000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2441341184 cell2441472256)
                  (ThetaLowerSegment.join cell2441603328 cell2441734400))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2441865472 cell2441996544)
                  (ThetaLowerSegment.join cell2442127616 cell2442258688)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2442389760 cell2442520832)
                  (ThetaLowerSegment.join cell2442651904 cell2442782976))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2442914048 cell2443045120)
                  (ThetaLowerSegment.join cell2443176192 cell2443307264))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2443438336 cell2443569408)
                  (ThetaLowerSegment.join cell2443700480 cell2443831552))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2443962624 cell2444093696)
                  (ThetaLowerSegment.join cell2444224768 cell2444355840)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2444486912 cell2444617984)
                  (ThetaLowerSegment.join cell2444749056 cell2444880128))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2445011200 cell2445142272)
                  (ThetaLowerSegment.join cell2445273344 cell2445404416)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2445535488 cell2445666560)
                  (ThetaLowerSegment.join cell2445797632 cell2445928704))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2446059776 cell2446190848)
                  (ThetaLowerSegment.join cell2446321920 cell2446452992)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2446584064 cell2446715136)
                  (ThetaLowerSegment.join cell2446846208 cell2446977280))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2447108352 cell2447239424)
                  (ThetaLowerSegment.join cell2447370496 cell2447501568))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2447632640 cell2447763712)
                  (ThetaLowerSegment.join cell2447894784 cell2448025856))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2448156928 cell2448288000)
                  (ThetaLowerSegment.join cell2448419072 cell2448550144)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2448681216 cell2448812288)
                  (ThetaLowerSegment.join cell2448943360 cell2449074432))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2449205504 cell2449336576)
                  (ThetaLowerSegment.join cell2449467648 cell2449598720))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2449729792 cell2449860864)
                  (ThetaLowerSegment.join cell2449991936 cell2450123008))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2450254080 cell2450385152)
                  (ThetaLowerSegment.join cell2450516224 cell2450647296)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2450778368 cell2450909440)
                  (ThetaLowerSegment.join cell2451040512 cell2451171584))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2451302656 cell2451433728)
                  (ThetaLowerSegment.join cell2451564800 cell2451695872))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2451826944 cell2451958016)
                  (ThetaLowerSegment.join cell2452089088 cell2452220160))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2452351232 cell2452482304)
                  (ThetaLowerSegment.join cell2452613376 cell2452744448)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2452875520 cell2453006592)
                  (ThetaLowerSegment.join cell2453137664 cell2453268736))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2453399808 cell2453530880)
                  (ThetaLowerSegment.join cell2453661952 cell2453793024)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2453924096 cell2454055168)
                  (ThetaLowerSegment.join cell2454186240 cell2454317312))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2454448384 cell2454579456)
                  (ThetaLowerSegment.join cell2454710528 cell2454841600)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2454972672 cell2455103744)
                  (ThetaLowerSegment.join cell2455234816 cell2455365888))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2455496960 cell2455628032)
                  (ThetaLowerSegment.join cell2455759104 cell2455890176))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2456021248 cell2456152320)
                  (ThetaLowerSegment.join cell2456283392 cell2456414464))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2456545536 cell2456676608)
                  (ThetaLowerSegment.join cell2456807680 cell2456938752)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2457069824 cell2457200896)
                  (ThetaLowerSegment.join cell2457331968 cell2457463040))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2457594112 cell2457725184)
                  (ThetaLowerSegment.join cell2457856256 cell2457987328)))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2458118400 cell2458249472)
                  (ThetaLowerSegment.join cell2458380544 cell2458511616))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2458642688 cell2458773760)
                  (ThetaLowerSegment.join cell2458904832 cell2459035904)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2459166976 cell2459298048)
                  (ThetaLowerSegment.join cell2459429120 cell2459560192))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2459691264 cell2459822336)
                  (ThetaLowerSegment.join cell2459953408 cell2460084480))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2460215552 cell2460346624)
                  (ThetaLowerSegment.join cell2460477696 cell2460608768))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2460739840 cell2460870912)
                  (ThetaLowerSegment.join cell2461001984 cell2461133056)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2461264128 cell2461395200)
                  (ThetaLowerSegment.join cell2461526272 cell2461657344))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2461788416 cell2461919488)
                  (ThetaLowerSegment.join cell2462050560 cell2462181632)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2462312704 cell2462443776)
                  (ThetaLowerSegment.join cell2462574848 cell2462705920))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2462836992 cell2462968064)
                  (ThetaLowerSegment.join cell2463099136 cell2463230208)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2463361280 cell2463492352)
                  (ThetaLowerSegment.join cell2463623424 cell2463754496))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2463885568 cell2464016640)
                  (ThetaLowerSegment.join cell2464147712 cell2464278784))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2464409856 cell2464540928)
                  (ThetaLowerSegment.join cell2464672000 cell2464803072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2464934144 cell2465065216)
                  (ThetaLowerSegment.join cell2465196288 cell2465327360)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2465458432 cell2465589504)
                  (ThetaLowerSegment.join cell2465720576 cell2465851648))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2465982720 cell2466113792)
                  (ThetaLowerSegment.join cell2466244864 cell2466375936))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2466507008 cell2466638080)
                  (ThetaLowerSegment.join cell2466769152 cell2466900224))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2467031296 cell2467162368)
                  (ThetaLowerSegment.join cell2467293440 cell2467424512)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2467555584 cell2467686656)
                  (ThetaLowerSegment.join cell2467817728 cell2467948800))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2468079872 cell2468210944)
                  (ThetaLowerSegment.join cell2468342016 cell2468473088))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2468604160 cell2468735232)
                  (ThetaLowerSegment.join cell2468866304 cell2468997376))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2469128448 cell2469259520)
                  (ThetaLowerSegment.join cell2469390592 cell2469521664)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2469652736 cell2469783808)
                  (ThetaLowerSegment.join cell2469914880 cell2470045952))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2470177024 cell2470308096)
                  (ThetaLowerSegment.join cell2470439168 cell2470570240)))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2470701312 cell2470832384)
                  (ThetaLowerSegment.join cell2470963456 cell2471094528))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2471225600 cell2471356672)
                  (ThetaLowerSegment.join cell2471487744 cell2471618816)))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2471749888 cell2471880960)
                  (ThetaLowerSegment.join cell2472012032 cell2472143104))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell2472274176 cell2472405248)
                  (ThetaLowerSegment.join cell2472536320 cell2472667392))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join (ThetaLowerSegment.join cell2472798464 cell2472929536)
                (ThetaLowerSegment.join cell2473060608 cell2473191680))
              (ThetaLowerSegment.join cell2473322752 cell2473339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
