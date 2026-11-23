/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.DirectThetaSegment
import all PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal.ThetaPackedBasis32768

/-! # Direct theta estimate up to 489341184 -/

@[expose] public section

namespace PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal

private theorem cell457341184 :
    ThetaLowerSegment 457341184 457406720 (45732012740827 / 100000) (9147681160597 / 20000) := by
  exact
    packedTile32768 457341184 457406720 13 3206 21385 29 _ _ (1994093 / 100000) (124631 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457406720 :
    ThetaLowerSegment 457406720 457472256 (9147681160597 / 20000) (285905977778 / 625) := by
  exact
    packedTile32768 457406720 457472256 13 3285 21387 29 _ _ (1994107 / 100000) (199411 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457472256 :
    ThetaLowerSegment 457472256 457537792 (285905977778 / 625) (11437872296219 / 25000) := by
  exact
    packedTile32768 457472256 457537792 13 3276 21388 29 _ _ (1994121 / 100000) (498531 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457537792 :
    ThetaLowerSegment 457537792 457603328 (11437872296219 / 25000) (11439522942293 / 25000) := by
  exact
    packedTile32768 457537792 457603328 13 3311 21390 29 _ _ (249267 / 12500) (1994139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457603328 :
    ThetaLowerSegment 457603328 457668864 (11439522942293 / 25000) (22882317287661 / 50000) := by
  exact
    packedTile32768 457603328 457668864 13 3281 21391 29 _ _ (39883 / 2000) (1994153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457668864 :
    ThetaLowerSegment 457668864 457734400 (22882317287661 / 50000) (22885592702031 / 50000) := by
  exact
    packedTile32768 457668864 457734400 13 3285 21393 29 _ _ (498541 / 25000) (1994167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457734400 :
    ThetaLowerSegment 457734400 457799936 (22885592702031 / 50000) (22888883095731 / 50000) := by
  exact
    packedTile32768 457734400 457799936 13 3300 21394 29 _ _ (997089 / 50000) (1994181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457799936 :
    ThetaLowerSegment 457799936 457865472 (22888883095731 / 50000) (2861514460323 / 6250) := by
  exact
    packedTile32768 457799936 457865472 13 3242 21396 29 _ _ (1994193 / 100000) (498549 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457865472 :
    ThetaLowerSegment 457865472 457931008 (2861514460323 / 6250) (45790818230889 / 100000) := by
  exact
    packedTile32768 457865472 457931008 13 3303 21397 29 _ _ (1994207 / 100000) (199421 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457931008 :
    ThetaLowerSegment 457931008 457996544 (45790818230889 / 100000) (5724656697757 / 12500) := by
  exact
    packedTile32768 457931008 457996544 13 3227 21399 29 _ _ (1994221 / 100000) (124639 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell457996544 :
    ThetaLowerSegment 457996544 458062080 (5724656697757 / 12500) (2862735920861 / 6250) := by
  exact
    packedTile32768 457996544 458062080 13 3270 21400 29 _ _ (498559 / 25000) (1994239 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458062080 :
    ThetaLowerSegment 458062080 458127616 (2862735920861 / 6250) (1431574863868 / 3125) := by
  exact
    packedTile32768 458062080 458127616 13 3320 21402 29 _ _ (7977 / 400) (1994253 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458127616 :
    ThetaLowerSegment 458127616 458193152 (1431574863868 / 3125) (5727123834353 / 12500) := by
  exact
    packedTile32768 458127616 458193152 13 3307 21403 29 _ _ (249283 / 12500) (1994267 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458193152 :
    ThetaLowerSegment 458193152 458258688 (5727123834353 / 12500) (45823573789803 / 100000) := by
  exact
    packedTile32768 458193152 458258688 13 3301 21405 29 _ _ (1994279 / 100000) (997141 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458258688 :
    ThetaLowerSegment 458258688 458324224 (45823573789803 / 100000) (11457539237749 / 25000) := by
  exact
    packedTile32768 458258688 458324224 13 3301 21406 29 _ _ (1994293 / 100000) (249287 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458324224 :
    ThetaLowerSegment 458324224 458389760 (11457539237749 / 25000) (5729574321749 / 12500) := by
  exact
    packedTile32768 458324224 458389760 13 3228 21408 29 _ _ (1994307 / 100000) (199431 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458389760 :
    ThetaLowerSegment 458389760 458455296 (5729574321749 / 12500) (22921553017661 / 50000) := by
  exact
    packedTile32768 458389760 458455296 13 3265 21410 29 _ _ (997161 / 50000) (79773 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458455296 :
    ThetaLowerSegment 458455296 458520832 (22921553017661 / 50000) (22924819740029 / 50000) := by
  exact
    packedTile32768 458455296 458520832 13 3276 21411 29 _ _ (62323 / 3125) (1994339 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458520832 :
    ThetaLowerSegment 458520832 458586368 (22924819740029 / 50000) (2866010935313 / 6250) := by
  exact
    packedTile32768 458520832 458586368 13 3277 21413 29 _ _ (39887 / 2000) (1994353 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458586368 :
    ThetaLowerSegment 458586368 458651904 (2866010935313 / 6250) (11465694576053 / 25000) := by
  exact
    packedTile32768 458586368 458651904 13 3311 21414 29 _ _ (498591 / 25000) (1994367 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458651904 :
    ThetaLowerSegment 458651904 458717440 (11465694576053 / 25000) (45869377704323 / 100000) := by
  exact
    packedTile32768 458651904 458717440 13 3309 21416 29 _ _ (1994379 / 100000) (997191 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458717440 :
    ThetaLowerSegment 458717440 458782976 (45869377704323 / 100000) (45875863470359 / 100000) := by
  exact
    packedTile32768 458717440 458782976 13 3252 21417 29 _ _ (1994393 / 100000) (498599 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458782976 :
    ThetaLowerSegment 458782976 458848512 (45875863470359 / 100000) (4588239116447 / 10000) := by
  exact
    packedTile32768 458782976 458848512 13 3273 21419 29 _ _ (1994407 / 100000) (199441 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458848512 :
    ThetaLowerSegment 458848512 458914048 (4588239116447 / 10000) (5736137300707 / 12500) := by
  exact
    packedTile32768 458848512 458914048 13 3363 21420 29 _ _ (997211 / 50000) (79777 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458914048 :
    ThetaLowerSegment 458914048 458979584 (5736137300707 / 12500) (11473862671079 / 25000) := by
  exact
    packedTile32768 458914048 458979584 13 3185 21422 29 _ _ (498609 / 25000) (1994439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell458979584 :
    ThetaLowerSegment 458979584 459045120 (11473862671079 / 25000) (5737750555877 / 12500) := by
  exact
    packedTile32768 458979584 459045120 13 3286 21423 29 _ _ (39889 / 2000) (1994453 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459045120 :
    ThetaLowerSegment 459045120 459110656 (5737750555877 / 12500) (5738579255669 / 12500) := by
  exact
    packedTile32768 459045120 459110656 13 3324 21425 29 _ _ (62327 / 3125) (1994467 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459110656 :
    ThetaLowerSegment 459110656 459176192 (5738579255669 / 12500) (11478811934429 / 25000) := by
  exact
    packedTile32768 459110656 459176192 13 3316 21426 29 _ _ (1994479 / 100000) (997241 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459176192 :
    ThetaLowerSegment 459176192 459241728 (11478811934429 / 25000) (45921827570123 / 100000) := by
  exact
    packedTile32768 459176192 459241728 13 3299 21428 29 _ _ (1994493 / 100000) (62328 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459241728 :
    ThetaLowerSegment 459241728 459307264 (45921827570123 / 100000) (22964181784781 / 50000) := by
  exact
    packedTile32768 459241728 459307264 13 3277 21429 29 _ _ (1994507 / 100000) (199451 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459307264 :
    ThetaLowerSegment 459307264 459372800 (22964181784781 / 50000) (22967488700599 / 50000) := by
  exact
    packedTile32768 459307264 459372800 13 3316 21431 29 _ _ (1994521 / 100000) (498631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459372800 :
    ThetaLowerSegment 459372800 459438336 (22967488700599 / 50000) (22970769712319 / 50000) := by
  exact
    packedTile32768 459372800 459438336 13 3290 21432 29 _ _ (249317 / 12500) (1994539 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459438336 :
    ThetaLowerSegment 459438336 459503872 (22970769712319 / 50000) (11487004929397 / 25000) := by
  exact
    packedTile32768 459438336 459503872 13 3249 21434 29 _ _ (39891 / 2000) (1994553 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459503872 :
    ThetaLowerSegment 459503872 459569408 (11487004929397 / 25000) (11488635485467 / 25000) := by
  exact
    packedTile32768 459503872 459569408 13 3270 21436 29 _ _ (498641 / 25000) (1994567 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459569408 :
    ThetaLowerSegment 459569408 459634944 (11488635485467 / 25000) (45961185884517 / 100000) := by
  exact
    packedTile32768 459569408 459634944 13 3331 21437 29 _ _ (1994579 / 100000) (997291 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459634944 :
    ThetaLowerSegment 459634944 459700480 (45961185884517 / 100000) (45967712192813 / 100000) := by
  exact
    packedTile32768 459634944 459700480 13 3272 21439 29 _ _ (1994593 / 100000) (498649 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459700480 :
    ThetaLowerSegment 459700480 459766016 (45967712192813 / 100000) (45974222590061 / 100000) := by
  exact
    packedTile32768 459700480 459766016 13 3264 21440 29 _ _ (1994607 / 100000) (199461 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459766016 :
    ThetaLowerSegment 459766016 459831552 (45974222590061 / 100000) (11495192732701 / 25000) := by
  exact
    packedTile32768 459766016 459831552 13 3283 21442 29 _ _ (1994621 / 100000) (62332 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459831552 :
    ThetaLowerSegment 459831552 459897088 (11495192732701 / 25000) (287420720822 / 625) := by
  exact
    packedTile32768 459831552 459897088 13 3281 21443 29 _ _ (498659 / 25000) (1994639 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459897088 :
    ThetaLowerSegment 459897088 459962624 (287420720822 / 625) (4599377600287 / 10000) := by
  exact
    packedTile32768 459897088 459962624 13 3239 21445 29 _ _ (39893 / 2000) (1994653 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell459962624 :
    ThetaLowerSegment 459962624 460028160 (4599377600287 / 10000) (23000186178359 / 50000) := by
  exact
    packedTile32768 459962624 460028160 13 3307 21446 29 _ _ (249333 / 12500) (1994667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460028160 :
    ThetaLowerSegment 460028160 460093696 (23000186178359 / 50000) (23003415562041 / 50000) := by
  exact
    packedTile32768 460028160 460093696 13 3238 21448 29 _ _ (997339 / 50000) (1994681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460093696 :
    ThetaLowerSegment 460093696 460159232 (23003415562041 / 50000) (46013423584447 / 100000) := by
  exact
    packedTile32768 460093696 460159232 13 3305 21449 29 _ _ (1994693 / 100000) (249337 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460159232 :
    ThetaLowerSegment 460159232 460224768 (46013423584447 / 100000) (23009936236089 / 50000) := by
  exact
    packedTile32768 460159232 460224768 13 3233 21451 29 _ _ (1994707 / 100000) (199471 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460224768 :
    ThetaLowerSegment 460224768 460290304 (23009936236089 / 50000) (23013227525739 / 50000) := by
  exact
    packedTile32768 460224768 460290304 13 3300 21452 29 _ _ (1994721 / 100000) (498681 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460290304 :
    ThetaLowerSegment 460290304 460355840 (23013227525739 / 50000) (46032963871783 / 100000) := by
  exact
    packedTile32768 460290304 460355840 13 3263 21454 29 _ _ (398947 / 20000) (997369 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460355840 :
    ThetaLowerSegment 460355840 460421376 (46032963871783 / 100000) (46039618357783 / 100000) := by
  exact
    packedTile32768 460355840 460421376 13 3336 21455 29 _ _ (7979 / 400) (1994753 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460421376 :
    ThetaLowerSegment 460421376 460486912 (46039618357783 / 100000) (46046153204647 / 100000) := by
  exact
    packedTile32768 460421376 460486912 13 3276 21457 29 _ _ (498691 / 25000) (1994767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460486912 :
    ThetaLowerSegment 460486912 460552448 (46046153204647 / 100000) (46052644212259 / 100000) := by
  exact
    packedTile32768 460486912 460552448 13 3254 21458 29 _ _ (997389 / 50000) (1994781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460552448 :
    ThetaLowerSegment 460552448 460617984 (46052644212259 / 100000) (46059135265427 / 100000) := by
  exact
    packedTile32768 460552448 460617984 13 3254 21460 29 _ _ (249349 / 12500) (398959 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460617984 :
    ThetaLowerSegment 460617984 460683520 (46059135265427 / 100000) (46065748047317 / 100000) := by
  exact
    packedTile32768 460617984 460683520 13 3315 21462 29 _ _ (997403 / 50000) (1994809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460683520 :
    ThetaLowerSegment 460683520 460749056 (46065748047317 / 100000) (3685790147 / 8) := by
  exact
    packedTile32768 460683520 460749056 13 3323 21463 29 _ _ (1994821 / 100000) (249353 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460749056 :
    ThetaLowerSegment 460749056 460814592 (3685790147 / 8) (9215790761699 / 20000) := by
  exact
    packedTile32768 460749056 460814592 13 3297 21465 29 _ _ (398967 / 20000) (997419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460814592 :
    ThetaLowerSegment 460814592 460880128 (9215790761699 / 20000) (1440171840877 / 3125) := by
  exact
    packedTile32768 460814592 460880128 13 3281 21466 29 _ _ (1994849 / 100000) (498713 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460880128 :
    ThetaLowerSegment 460880128 460945664 (1440171840877 / 3125) (23045975147503 / 50000) := by
  exact
    packedTile32768 460880128 460945664 13 3234 21468 29 _ _ (1994863 / 100000) (997433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell460945664 :
    ThetaLowerSegment 460945664 461011200 (23045975147503 / 50000) (4609848950509 / 10000) := by
  exact
    packedTile32768 460945664 461011200 13 3278 21469 29 _ _ (997439 / 50000) (1994881 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461011200 :
    ThetaLowerSegment 461011200 461076736 (4609848950509 / 10000) (23052582206861 / 50000) := by
  exact
    packedTile32768 461011200 461076736 13 3346 21471 29 _ _ (498723 / 25000) (398979 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461076736 :
    ThetaLowerSegment 461076736 461142272 (23052582206861 / 50000) (5763960221453 / 12500) := by
  exact
    packedTile32768 461076736 461142272 13 3267 21472 29 _ _ (997453 / 50000) (1994909 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461142272 :
    ThetaLowerSegment 461142272 461207808 (5763960221453 / 12500) (5764777639923 / 12500) := by
  exact
    packedTile32768 461142272 461207808 13 3278 21474 29 _ _ (49873 / 2500) (1994923 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461207808 :
    ThetaLowerSegment 461207808 461273344 (5764777639923 / 12500) (2882800275099 / 6250) := by
  exact
    packedTile32768 461207808 461273344 13 3300 21475 29 _ _ (997467 / 50000) (1994937 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461273344 :
    ThetaLowerSegment 461273344 461338880 (2882800275099 / 6250) (46131437607009 / 100000) := by
  exact
    packedTile32768 461273344 461338880 13 3325 21477 29 _ _ (1994949 / 100000) (249369 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461338880 :
    ThetaLowerSegment 461338880 461404416 (46131437607009 / 100000) (9227585045337 / 20000) := by
  exact
    packedTile32768 461338880 461404416 13 3252 21478 29 _ _ (1994963 / 100000) (997483 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461404416 :
    ThetaLowerSegment 461404416 461469952 (9227585045337 / 20000) (46144341072717 / 100000) := by
  exact
    packedTile32768 461404416 461469952 13 3216 21480 29 _ _ (1994977 / 100000) (99749 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461469952 :
    ThetaLowerSegment 461469952 461535488 (46144341072717 / 100000) (2884425926157 / 6250) := by
  exact
    packedTile32768 461469952 461535488 13 3245 21481 29 _ _ (1994991 / 100000) (997497 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461535488 :
    ThetaLowerSegment 461535488 461601024 (2884425926157 / 6250) (5769683769399 / 12500) := by
  exact
    packedTile32768 461535488 461601024 13 3336 21483 29 _ _ (399001 / 20000) (62344 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461601024 :
    ThetaLowerSegment 461601024 461666560 (5769683769399 / 12500) (11541026896683 / 25000) := by
  exact
    packedTile32768 461601024 461666560 13 3327 21484 29 _ _ (99751 / 5000) (1995023 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461666560 :
    ThetaLowerSegment 461666560 461732096 (11541026896683 / 25000) (23085250835351 / 50000) := by
  exact
    packedTile32768 461666560 461732096 13 3205 21486 29 _ _ (997517 / 50000) (1995037 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461732096 :
    ThetaLowerSegment 461732096 461797632 (23085250835351 / 50000) (23088542664551 / 50000) := by
  exact
    packedTile32768 461732096 461797632 13 3300 21487 29 _ _ (249381 / 12500) (1995051 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461797632 :
    ThetaLowerSegment 461797632 461863168 (23088542664551 / 50000) (23091836511913 / 50000) := by
  exact
    packedTile32768 461797632 461863168 13 3302 21489 29 _ _ (997531 / 50000) (399013 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461863168 :
    ThetaLowerSegment 461863168 461928704 (23091836511913 / 50000) (23095135370079 / 50000) := by
  exact
    packedTile32768 461863168 461928704 13 3307 21491 29 _ _ (498769 / 25000) (1995079 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461928704 :
    ThetaLowerSegment 461928704 461994240 (23095135370079 / 50000) (11549212637569 / 25000) := by
  exact
    packedTile32768 461928704 461994240 13 3298 21492 29 _ _ (1995091 / 100000) (997547 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell461994240 :
    ThetaLowerSegment 461994240 462059776 (11549212637569 / 25000) (46203504225451 / 100000) := by
  exact
    packedTile32768 461994240 462059776 13 3335 21494 29 _ _ (399021 / 20000) (498777 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462059776 :
    ThetaLowerSegment 462059776 462125312 (46203504225451 / 100000) (46210044225533 / 100000) := by
  exact
    packedTile32768 462059776 462125312 13 3278 21495 29 _ _ (1995119 / 100000) (997561 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462125312 :
    ThetaLowerSegment 462125312 462190848 (46210044225533 / 100000) (23108275177123 / 50000) := by
  exact
    packedTile32768 462125312 462190848 13 3261 21497 29 _ _ (1995133 / 100000) (62348 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462190848 :
    ThetaLowerSegment 462190848 462256384 (23108275177123 / 50000) (46223052538319 / 100000) := by
  exact
    packedTile32768 462190848 462256384 13 3259 21498 29 _ _ (1995147 / 100000) (39903 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462256384 :
    ThetaLowerSegment 462256384 462321920 (46223052538319 / 100000) (46229594674517 / 100000) := by
  exact
    packedTile32768 462256384 462321920 13 3279 21500 29 _ _ (997581 / 50000) (399033 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462321920 :
    ThetaLowerSegment 462321920 462387456 (46229594674517 / 100000) (46236027121941 / 100000) := by
  exact
    packedTile32768 462321920 462387456 13 3224 21501 29 _ _ (249397 / 12500) (1995179 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462387456 :
    ThetaLowerSegment 462387456 462452992 (46236027121941 / 100000) (46242645167171 / 100000) := by
  exact
    packedTile32768 462387456 462452992 13 3317 21503 29 _ _ (199519 / 10000) (1995193 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462452992 :
    ThetaLowerSegment 462452992 462518528 (46242645167171 / 100000) (46249309148531 / 100000) := by
  exact
    packedTile32768 462452992 462518528 13 3340 21504 29 _ _ (498801 / 25000) (1995207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462518528 :
    ThetaLowerSegment 462518528 462584064 (46249309148531 / 100000) (46255961205343 / 100000) := by
  exact
    packedTile32768 462518528 462584064 13 3334 21506 29 _ _ (997609 / 50000) (1995221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462584064 :
    ThetaLowerSegment 462584064 462649600 (46255961205343 / 100000) (46262653213471 / 100000) := by
  exact
    packedTile32768 462584064 462649600 13 3354 21507 29 _ _ (62351 / 3125) (399047 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462649600 :
    ThetaLowerSegment 462649600 462715136 (46262653213471 / 100000) (46269257481041 / 100000) := by
  exact
    packedTile32768 462649600 462715136 13 3310 21509 29 _ _ (1995247 / 100000) (7981 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462715136 :
    ThetaLowerSegment 462715136 462780672 (46269257481041 / 100000) (46275821889731 / 100000) := by
  exact
    packedTile32768 462715136 462780672 13 3290 21510 29 _ _ (1995261 / 100000) (62352 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462780672 :
    ThetaLowerSegment 462780672 462846208 (46275821889731 / 100000) (46282282590181 / 100000) := by
  exact
    packedTile32768 462780672 462846208 13 3238 21512 29 _ _ (79811 / 4000) (997639 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462846208 :
    ThetaLowerSegment 462846208 462911744 (46282282590181 / 100000) (46288783241743 / 100000) := by
  exact
    packedTile32768 462846208 462911744 13 3258 21513 29 _ _ (1995289 / 100000) (498823 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462911744 :
    ThetaLowerSegment 462911744 462977280 (46288783241743 / 100000) (46295467506793 / 100000) := by
  exact
    packedTile32768 462911744 462977280 13 3350 21515 29 _ _ (1995303 / 100000) (997653 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell462977280 :
    ThetaLowerSegment 462977280 463042816 (46295467506793 / 100000) (46302079987331 / 100000) := by
  exact
    packedTile32768 462977280 463042816 13 3314 21516 29 _ _ (1995317 / 100000) (49883 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463042816 :
    ThetaLowerSegment 463042816 463108352 (46302079987331 / 100000) (46308666578263 / 100000) := by
  exact
    packedTile32768 463042816 463108352 13 3301 21518 29 _ _ (498833 / 25000) (399067 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463108352 :
    ThetaLowerSegment 463108352 463173888 (46308666578263 / 100000) (46315053680809 / 100000) := by
  exact
    packedTile32768 463108352 463173888 13 3201 21519 29 _ _ (997673 / 50000) (1995349 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463173888 :
    ThetaLowerSegment 463173888 463239424 (46315053680809 / 100000) (46321658322409 / 100000) := by
  exact
    packedTile32768 463173888 463239424 13 3310 21521 29 _ _ (12471 / 625) (1995363 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463239424 :
    ThetaLowerSegment 463239424 463304960 (46321658322409 / 100000) (74125137809 / 160) := by
  exact
    packedTile32768 463239424 463304960 13 3284 21522 29 _ _ (997687 / 50000) (1995377 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463304960 :
    ThetaLowerSegment 463304960 463370496 (74125137809 / 160) (9266963172981 / 20000) := by
  exact
    packedTile32768 463304960 463370496 13 3310 21524 29 _ _ (498847 / 25000) (1995391 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463370496 :
    ThetaLowerSegment 463370496 463436032 (9266963172981 / 20000) (1853652835017 / 4000) := by
  exact
    packedTile32768 463370496 463436032 13 3260 21526 29 _ _ (997701 / 50000) (399081 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463436032 :
    ThetaLowerSegment 463436032 463501568 (1853652835017 / 4000) (46347929693217 / 100000) := by
  exact
    packedTile32768 463436032 463501568 13 3312 21527 29 _ _ (249427 / 12500) (1995419 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463501568 :
    ThetaLowerSegment 463501568 463567104 (46347929693217 / 100000) (1854178030469 / 4000) := by
  exact
    packedTile32768 463501568 463567104 13 3268 21529 29 _ _ (1995431 / 100000) (997717 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463567104 :
    ThetaLowerSegment 463567104 463632640 (1854178030469 / 4000) (2318051686739 / 5000) := by
  exact
    packedTile32768 463567104 463632640 13 3299 21530 29 _ _ (399089 / 20000) (249431 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463632640 :
    ThetaLowerSegment 463632640 463698176 (2318051686739 / 5000) (46367540926579 / 100000) := by
  exact
    packedTile32768 463632640 463698176 13 3261 21532 29 _ _ (1995459 / 100000) (997731 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463698176 :
    ThetaLowerSegment 463698176 463763712 (46367540926579 / 100000) (46374034195721 / 100000) := by
  exact
    packedTile32768 463698176 463763712 13 3254 21533 29 _ _ (1995473 / 100000) (498869 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463763712 :
    ThetaLowerSegment 463763712 463829248 (46374034195721 / 100000) (5797584646493 / 12500) := by
  exact
    packedTile32768 463763712 463829248 13 3329 21535 29 _ _ (1995487 / 100000) (199549 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463829248 :
    ThetaLowerSegment 463829248 463894784 (5797584646493 / 12500) (46387276293751 / 100000) := by
  exact
    packedTile32768 463829248 463894784 13 3307 21536 29 _ _ (1995501 / 100000) (124719 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463894784 :
    ThetaLowerSegment 463894784 463960320 (46387276293751 / 100000) (46393901403551 / 100000) := by
  exact
    packedTile32768 463894784 463960320 13 3320 21538 29 _ _ (399103 / 20000) (997759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell463960320 :
    ThetaLowerSegment 463960320 464025856 (46393901403551 / 100000) (9280087751311 / 20000) := by
  exact
    packedTile32768 463960320 464025856 13 3276 21539 29 _ _ (1995529 / 100000) (498883 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464025856 :
    ThetaLowerSegment 464025856 464091392 (9280087751311 / 20000) (46406866403779 / 100000) := by
  exact
    packedTile32768 464025856 464091392 13 3221 21541 29 _ _ (249443 / 12500) (1995547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464091392 :
    ThetaLowerSegment 464091392 464156928 (46406866403779 / 100000) (46413393873997 / 100000) := by
  exact
    packedTile32768 464091392 464156928 13 3271 21542 29 _ _ (997779 / 50000) (1995561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464156928 :
    ThetaLowerSegment 464156928 464222464 (46413393873997 / 100000) (46419959305877 / 100000) := by
  exact
    packedTile32768 464156928 464222464 13 3290 21544 29 _ _ (498893 / 25000) (79823 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464222464 :
    ThetaLowerSegment 464222464 464288000 (46419959305877 / 100000) (46426514805887 / 100000) := by
  exact
    packedTile32768 464222464 464288000 13 3285 21545 29 _ _ (997793 / 50000) (1995589 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464288000 :
    ThetaLowerSegment 464288000 464353536 (46426514805887 / 100000) (46433134211087 / 100000) := by
  exact
    packedTile32768 464288000 464353536 13 3317 21547 29 _ _ (4989 / 250) (1995603 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464353536 :
    ThetaLowerSegment 464353536 464419072 (46433134211087 / 100000) (46439677829393 / 100000) := by
  exact
    packedTile32768 464353536 464419072 13 3279 21548 29 _ _ (997807 / 50000) (1995617 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464419072 :
    ThetaLowerSegment 464419072 464484608 (46439677829393 / 100000) (46446269388677 / 100000) := by
  exact
    packedTile32768 464419072 464484608 13 3303 21550 29 _ _ (498907 / 25000) (1995631 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464484608 :
    ThetaLowerSegment 464484608 464550144 (46446269388677 / 100000) (46452665421287 / 100000) := by
  exact
    packedTile32768 464484608 464550144 13 3205 21551 29 _ _ (997821 / 50000) (399129 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464550144 :
    ThetaLowerSegment 464550144 464615680 (46452665421287 / 100000) (46459215167561 / 100000) := by
  exact
    packedTile32768 464550144 464615680 13 3282 21553 29 _ _ (1995657 / 100000) (99783 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464615680 :
    ThetaLowerSegment 464615680 464681216 (46459215167561 / 100000) (11616438745357 / 25000) := by
  exact
    packedTile32768 464615680 464681216 13 3277 21554 29 _ _ (1995671 / 100000) (997837 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464681216 :
    ThetaLowerSegment 464681216 464746752 (11616438745357 / 25000) (46472386642683 / 100000) := by
  exact
    packedTile32768 464681216 464746752 13 3323 21556 29 _ _ (399137 / 20000) (249461 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464746752 :
    ThetaLowerSegment 464746752 464812288 (46472386642683 / 100000) (11619710682237 / 25000) := by
  exact
    packedTile32768 464746752 464812288 13 3235 21557 29 _ _ (1995699 / 100000) (997851 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464812288 :
    ThetaLowerSegment 464812288 464877824 (11619710682237 / 25000) (11621371115453 / 25000) := by
  exact
    packedTile32768 464812288 464877824 13 3328 21559 29 _ _ (1995713 / 100000) (498929 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464877824 :
    ThetaLowerSegment 464877824 464943360 (11621371115453 / 25000) (5811498816479 / 12500) := by
  exact
    packedTile32768 464877824 464943360 13 3260 21561 29 _ _ (1995727 / 100000) (199573 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell464943360 :
    ThetaLowerSegment 464943360 465008896 (5811498816479 / 12500) (2324925630671 / 5000) := by
  exact
    packedTile32768 464943360 465008896 13 3268 21562 29 _ _ (1995741 / 100000) (62367 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465008896 :
    ThetaLowerSegment 465008896 465074432 (2324925630671 / 5000) (2325260119209 / 5000) := by
  exact
    packedTile32768 465008896 465074432 13 3352 21564 29 _ _ (399151 / 20000) (997879 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465074432 :
    ThetaLowerSegment 465074432 465139968 (2325260119209 / 5000) (5813965569659 / 12500) := by
  exact
    packedTile32768 465074432 465139968 13 3268 21565 29 _ _ (1995769 / 100000) (498943 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465139968 :
    ThetaLowerSegment 465139968 465205504 (5813965569659 / 12500) (4651832261587 / 10000) := by
  exact
    packedTile32768 465139968 465205504 13 3306 21567 29 _ _ (1995783 / 100000) (997893 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465205504 :
    ThetaLowerSegment 465205504 465271040 (4651832261587 / 10000) (4652486883003 / 10000) := by
  exact
    packedTile32768 465205504 465271040 13 3280 21568 29 _ _ (1995797 / 100000) (9979 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465271040 :
    ThetaLowerSegment 465271040 465336576 (4652486883003 / 10000) (23265671622079 / 50000) := by
  exact
    packedTile32768 465271040 465336576 13 3244 21570 29 _ _ (498953 / 25000) (399163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465336576 :
    ThetaLowerSegment 465336576 465402112 (23265671622079 / 50000) (23268962739153 / 50000) := by
  exact
    packedTile32768 465336576 465402112 13 3298 21571 29 _ _ (997913 / 50000) (1995829 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465402112 :
    ThetaLowerSegment 465402112 465467648 (23268962739153 / 50000) (23272237912593 / 50000) := by
  exact
    packedTile32768 465402112 465467648 13 3282 21573 29 _ _ (12474 / 625) (1995843 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465467648 :
    ThetaLowerSegment 465467648 465533184 (23272237912593 / 50000) (11637725119803 / 25000) := by
  exact
    packedTile32768 465467648 465533184 13 3219 21574 29 _ _ (997927 / 50000) (1995857 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465533184 :
    ThetaLowerSegment 465533184 465598720 (11637725119803 / 25000) (2327877934743 / 5000) := by
  exact
    packedTile32768 465533184 465598720 13 3336 21576 29 _ _ (498967 / 25000) (1995871 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465598720 :
    ThetaLowerSegment 465598720 465664256 (2327877934743 / 5000) (4656405529077 / 10000) := by
  exact
    packedTile32768 465598720 465664256 13 3255 21577 29 _ _ (997941 / 50000) (399177 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465664256 :
    ThetaLowerSegment 465664256 465729792 (4656405529077 / 10000) (4657067168601 / 10000) := by
  exact
    packedTile32768 465664256 465729792 13 3315 21579 29 _ _ (249487 / 12500) (1995899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465729792 :
    ThetaLowerSegment 465729792 465795328 (4657067168601 / 10000) (291107626667 / 625) := by
  exact
    packedTile32768 465729792 465795328 13 3281 21580 29 _ _ (199591 / 10000) (1995913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465795328 :
    ThetaLowerSegment 465795328 465860864 (291107626667 / 625) (1455741218602 / 3125) := by
  exact
    packedTile32768 465795328 465860864 13 3256 21582 29 _ _ (498981 / 25000) (1995927 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465860864 :
    ThetaLowerSegment 465860864 465926400 (1455741218602 / 3125) (2911896594339 / 6250) := by
  exact
    packedTile32768 465860864 465926400 13 3320 21583 29 _ _ (997969 / 50000) (1995941 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465926400 :
    ThetaLowerSegment 465926400 465991936 (2911896594339 / 6250) (2912308508933 / 6250) := by
  exact
    packedTile32768 465926400 465991936 13 3302 21585 29 _ _ (124747 / 6250) (399191 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell465991936 :
    ThetaLowerSegment 465991936 466057472 (2912308508933 / 6250) (582544334779 / 1250) := by
  exact
    packedTile32768 465991936 466057472 13 3312 21586 29 _ _ (997983 / 50000) (1995969 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466057472 :
    ThetaLowerSegment 466057472 466123008 (582544334779 / 1250) (1165252240119 / 2500) := by
  exact
    packedTile32768 466057472 466123008 13 3278 21588 29 _ _ (99799 / 5000) (1995983 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466123008 :
    ThetaLowerSegment 466123008 466188544 (1165252240119 / 2500) (9323326894473 / 20000) := by
  exact
    packedTile32768 466123008 466188544 13 3279 21589 29 _ _ (399199 / 20000) (997999 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466188544 :
    ThetaLowerSegment 466188544 466254080 (9323326894473 / 20000) (23311619633073 / 50000) := by
  exact
    packedTile32768 466188544 466254080 13 3309 21591 29 _ _ (1996009 / 100000) (499003 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466254080 :
    ThetaLowerSegment 466254080 466319616 (23311619633073 / 50000) (932594446977 / 2000) := by
  exact
    packedTile32768 466254080 466319616 13 3248 21592 29 _ _ (1996023 / 100000) (998013 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466319616 :
    ThetaLowerSegment 466319616 466385152 (932594446977 / 2000) (46636271346247 / 100000) := by
  exact
    packedTile32768 466319616 466385152 13 3281 21594 29 _ _ (1996037 / 100000) (49901 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466385152 :
    ThetaLowerSegment 466385152 466450688 (46636271346247 / 100000) (46642870290853 / 100000) := by
  exact
    packedTile32768 466385152 466450688 13 3306 21595 29 _ _ (1996051 / 100000) (998027 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466450688 :
    ThetaLowerSegment 466450688 466516224 (46642870290853 / 100000) (46649541140083 / 100000) := by
  exact
    packedTile32768 466450688 466516224 13 3342 21597 29 _ _ (399213 / 20000) (499017 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466516224 :
    ThetaLowerSegment 466516224 466581760 (46649541140083 / 100000) (11664009594307 / 25000) := by
  exact
    packedTile32768 466516224 466581760 13 3255 21598 29 _ _ (1996079 / 100000) (998041 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466581760 :
    ThetaLowerSegment 466581760 466647296 (11664009594307 / 25000) (46662559613059 / 100000) := by
  exact
    packedTile32768 466581760 466647296 13 3267 21600 29 _ _ (1996093 / 100000) (62378 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466647296 :
    ThetaLowerSegment 466647296 466712832 (46662559613059 / 100000) (11667286192513 / 25000) := by
  exact
    packedTile32768 466647296 466712832 13 3299 21602 29 _ _ (1996107 / 100000) (199611 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466712832 :
    ThetaLowerSegment 466712832 466778368 (11667286192513 / 25000) (46675626174939 / 100000) := by
  exact
    packedTile32768 466712832 466778368 13 3247 21603 29 _ _ (1996121 / 100000) (499031 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466778368 :
    ThetaLowerSegment 466778368 466843904 (46675626174939 / 100000) (5835270439633 / 12500) := by
  exact
    packedTile32768 466778368 466843904 13 3275 21605 29 _ _ (399227 / 20000) (998069 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466843904 :
    ThetaLowerSegment 466843904 466909440 (5835270439633 / 12500) (23344397362021 / 50000) := by
  exact
    packedTile32768 466843904 466909440 13 3322 21606 29 _ _ (1996149 / 100000) (249519 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466909440 :
    ThetaLowerSegment 466909440 466974976 (23344397362021 / 50000) (46695392042757 / 100000) := by
  exact
    packedTile32768 466909440 466974976 13 3305 21608 29 _ _ (1996163 / 100000) (998083 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell466974976 :
    ThetaLowerSegment 466974976 467040512 (46695392042757 / 100000) (4670211716307 / 10000) := by
  exact
    packedTile32768 466974976 467040512 13 3369 21609 29 _ _ (1996177 / 100000) (99809 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467040512 :
    ThetaLowerSegment 467040512 467106048 (4670211716307 / 10000) (46708538909517 / 100000) := by
  exact
    packedTile32768 467040512 467106048 13 3217 21611 29 _ _ (1996191 / 100000) (998097 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467106048 :
    ThetaLowerSegment 467106048 467171584 (46708538909517 / 100000) (23357476358091 / 50000) := by
  exact
    packedTile32768 467106048 467171584 13 3213 21612 29 _ _ (399241 / 20000) (124763 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467171584 :
    ThetaLowerSegment 467171584 467237120 (23357476358091 / 50000) (292009152391 / 625) := by
  exact
    packedTile32768 467171584 467237120 13 3262 21614 29 _ _ (1996219 / 100000) (998111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467237120 :
    ThetaLowerSegment 467237120 467302656 (292009152391 / 625) (1460253370187 / 3125) := by
  exact
    packedTile32768 467237120 467302656 13 3328 21615 29 _ _ (1996233 / 100000) (499059 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467302656 :
    ThetaLowerSegment 467302656 467368192 (1460253370187 / 3125) (1460456987381 / 3125) := by
  exact
    packedTile32768 467302656 467368192 13 3264 21617 29 _ _ (1996247 / 100000) (1597 / 80)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467368192 :
    ThetaLowerSegment 467368192 467433728 (1460456987381 / 3125) (9348227479167 / 20000) := by
  exact
    packedTile32768 467368192 467433728 13 3263 21618 29 _ _ (1996261 / 100000) (249533 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467433728 :
    ThetaLowerSegment 467433728 467499264 (9348227479167 / 20000) (2337386953863 / 5000) := by
  exact
    packedTile32768 467433728 467499264 13 3307 21620 29 _ _ (79851 / 4000) (998139 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467499264 :
    ThetaLowerSegment 467499264 467564800 (2337386953863 / 5000) (935086935877 / 2000) := by
  exact
    packedTile32768 467499264 467564800 13 3310 21621 29 _ _ (1996289 / 100000) (499073 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467564800 :
    ThetaLowerSegment 467564800 467630336 (935086935877 / 2000) (1461284571119 / 3125) := by
  exact
    packedTile32768 467564800 467630336 13 3386 21623 29 _ _ (1996303 / 100000) (998153 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467630336 :
    ThetaLowerSegment 467630336 467695872 (1461284571119 / 3125) (9353511275207 / 20000) := by
  exact
    packedTile32768 467630336 467695872 13 3231 21624 29 _ _ (1996317 / 100000) (12477 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467695872 :
    ThetaLowerSegment 467695872 467761408 (9353511275207 / 20000) (5846758800511 / 12500) := by
  exact
    packedTile32768 467695872 467761408 13 3263 21626 29 _ _ (1996331 / 100000) (998167 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467761408 :
    ThetaLowerSegment 467761408 467826944 (5846758800511 / 12500) (46780724221973 / 100000) := by
  exact
    packedTile32768 467761408 467826944 13 3333 21627 29 _ _ (399269 / 20000) (499087 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467826944 :
    ThetaLowerSegment 467826944 467892480 (46780724221973 / 100000) (4678727826857 / 10000) := by
  exact
    packedTile32768 467826944 467892480 13 3283 21629 29 _ _ (1996359 / 100000) (998181 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467892480 :
    ThetaLowerSegment 467892480 467958016 (4678727826857 / 10000) (46793872288589 / 100000) := by
  exact
    packedTile32768 467892480 467958016 13 3303 21630 29 _ _ (1996373 / 100000) (249547 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell467958016 :
    ThetaLowerSegment 467958016 468023552 (46793872288589 / 100000) (46800460365689 / 100000) := by
  exact
    packedTile32768 467958016 468023552 13 3300 21632 29 _ _ (1996387 / 100000) (199639 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468023552 :
    ThetaLowerSegment 468023552 468089088 (46800460365689 / 100000) (936139412587 / 2000) := by
  exact
    packedTile32768 468023552 468089088 13 3261 21633 29 _ _ (1996401 / 100000) (499101 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468089088 :
    ThetaLowerSegment 468089088 468154624 (936139412587 / 2000) (9362698583431 / 20000) := by
  exact
    packedTile32768 468089088 468154624 13 3267 21635 29 _ _ (399283 / 20000) (998209 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468154624 :
    ThetaLowerSegment 468154624 468220160 (9362698583431 / 20000) (46820017247127 / 100000) := by
  exact
    packedTile32768 468154624 468220160 13 3268 21636 29 _ _ (1996429 / 100000) (124777 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468220160 :
    ThetaLowerSegment 468220160 468285696 (46820017247127 / 100000) (46826469750903 / 100000) := by
  exact
    packedTile32768 468220160 468285696 13 3232 21638 29 _ _ (1996443 / 100000) (998223 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468285696 :
    ThetaLowerSegment 468285696 468351232 (46826469750903 / 100000) (46832994172379 / 100000) := by
  exact
    packedTile32768 468285696 468351232 13 3268 21639 29 _ _ (1996457 / 100000) (99823 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468351232 :
    ThetaLowerSegment 468351232 468416768 (46832994172379 / 100000) (5854949562747 / 12500) := by
  exact
    packedTile32768 468351232 468416768 13 3307 21641 29 _ _ (1996471 / 100000) (998237 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468416768 :
    ThetaLowerSegment 468416768 468482304 (5854949562747 / 12500) (5855780100507 / 12500) := by
  exact
    packedTile32768 468416768 468482304 13 3328 21642 29 _ _ (399297 / 20000) (249561 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468482304 :
    ThetaLowerSegment 468482304 468547840 (5855780100507 / 12500) (46852739408301 / 100000) := by
  exact
    packedTile32768 468482304 468547840 13 3255 21644 29 _ _ (1996499 / 100000) (998251 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468547840 :
    ThetaLowerSegment 468547840 468613376 (46852739408301 / 100000) (23429688907013 / 50000) := by
  exact
    packedTile32768 468547840 468613376 13 3325 21645 29 _ _ (1996513 / 100000) (499129 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468613376 :
    ThetaLowerSegment 468613376 468678912 (23429688907013 / 50000) (1464559826357 / 3125) := by
  exact
    packedTile32768 468613376 468678912 13 3274 21647 29 _ _ (1996527 / 100000) (199653 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468678912 :
    ThetaLowerSegment 468678912 468744448 (1464559826357 / 3125) (9374497011971 / 20000) := by
  exact
    packedTile32768 468678912 468744448 13 3291 21648 29 _ _ (1996541 / 100000) (62392 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468744448 :
    ThetaLowerSegment 468744448 468809984 (9374497011971 / 20000) (585987597563 / 1250) := by
  exact
    packedTile32768 468744448 468809984 13 3267 21650 29 _ _ (399311 / 20000) (998279 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468809984 :
    ThetaLowerSegment 468809984 468875520 (585987597563 / 1250) (46885554554791 / 100000) := by
  exact
    packedTile32768 468809984 468875520 13 3279 21652 29 _ _ (1996569 / 100000) (499143 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468875520 :
    ThetaLowerSegment 468875520 468941056 (46885554554791 / 100000) (9378443829769 / 20000) := by
  exact
    packedTile32768 468875520 468941056 13 3338 21653 29 _ _ (1996583 / 100000) (998293 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell468941056 :
    ThetaLowerSegment 468941056 469006592 (9378443829769 / 20000) (11724681514617 / 25000) := by
  exact
    packedTile32768 468941056 469006592 13 3259 21655 29 _ _ (1996597 / 100000) (9983 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469006592 :
    ThetaLowerSegment 469006592 469072128 (11724681514617 / 25000) (46905237006939 / 100000) := by
  exact
    packedTile32768 469006592 469072128 13 3261 21656 29 _ _ (1996611 / 100000) (998307 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469072128 :
    ThetaLowerSegment 469072128 469137664 (46905237006939 / 100000) (46911742011189 / 100000) := by
  exact
    packedTile32768 469072128 469137664 13 3258 21658 29 _ _ (15973 / 800) (499157 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469137664 :
    ThetaLowerSegment 469137664 469203200 (46911742011189 / 100000) (23459140501957 / 50000) := by
  exact
    packedTile32768 469137664 469203200 13 3275 21659 29 _ _ (1996639 / 100000) (998321 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469203200 :
    ThetaLowerSegment 469203200 469268736 (23459140501957 / 50000) (5865593270791 / 12500) := by
  exact
    packedTile32768 469203200 469268736 13 3238 21661 29 _ _ (1996653 / 100000) (124791 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469268736 :
    ThetaLowerSegment 469268736 469334272 (5865593270791 / 12500) (46931289244087 / 100000) := by
  exact
    packedTile32768 469268736 469334272 13 3277 21662 29 _ _ (1996667 / 100000) (199667 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469334272 :
    ThetaLowerSegment 469334272 469399808 (46931289244087 / 100000) (23468930160629 / 50000) := by
  exact
    packedTile32768 469334272 469399808 13 3291 21664 29 _ _ (1996681 / 100000) (499171 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469399808 :
    ThetaLowerSegment 469399808 469465344 (23468930160629 / 50000) (46944447418063 / 100000) := by
  exact
    packedTile32768 469399808 469465344 13 3299 21665 29 _ _ (399339 / 20000) (998349 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469465344 :
    ThetaLowerSegment 469465344 469530880 (46944447418063 / 100000) (46950980649911 / 100000) := by
  exact
    packedTile32768 469465344 469530880 13 3272 21667 29 _ _ (1996709 / 100000) (249589 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469530880 :
    ThetaLowerSegment 469530880 469596416 (46950980649911 / 100000) (23478789909713 / 50000) := by
  exact
    packedTile32768 469530880 469596416 13 3305 21668 29 _ _ (1996723 / 100000) (998363 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469596416 :
    ThetaLowerSegment 469596416 469661952 (23478789909713 / 50000) (2935249833259 / 6250) := by
  exact
    packedTile32768 469596416 469661952 13 3214 21670 29 _ _ (1996737 / 100000) (99837 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469661952 :
    ThetaLowerSegment 469661952 469727488 (2935249833259 / 6250) (46970520717661 / 100000) := by
  exact
    packedTile32768 469661952 469727488 13 3267 21671 29 _ _ (1996751 / 100000) (998377 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469727488 :
    ThetaLowerSegment 469727488 469793024 (46970520717661 / 100000) (23488524071223 / 50000) := by
  exact
    packedTile32768 469727488 469793024 13 3269 21673 29 _ _ (399353 / 20000) (62399 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469793024 :
    ThetaLowerSegment 469793024 469858560 (23488524071223 / 50000) (23491778820993 / 50000) := by
  exact
    packedTile32768 469793024 469858560 13 3260 21674 29 _ _ (1996779 / 100000) (998391 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469858560 :
    ThetaLowerSegment 469858560 469924096 (23491778820993 / 50000) (46990129087749 / 100000) := by
  exact
    packedTile32768 469858560 469924096 13 3291 21676 29 _ _ (1996793 / 100000) (499199 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469924096 :
    ThetaLowerSegment 469924096 469989632 (46990129087749 / 100000) (46996686601937 / 100000) := by
  exact
    packedTile32768 469924096 469989632 13 3284 21677 29 _ _ (1996807 / 100000) (199681 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell469989632 :
    ThetaLowerSegment 469989632 470055168 (46996686601937 / 100000) (5875427235691 / 12500) := by
  exact
    packedTile32768 469989632 470055168 13 3371 21679 29 _ _ (1996821 / 100000) (249603 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470055168 :
    ThetaLowerSegment 470055168 470120704 (5875427235691 / 12500) (47009881640423 / 100000) := by
  exact
    packedTile32768 470055168 470120704 13 3237 21680 29 _ _ (399367 / 20000) (998419 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470120704 :
    ThetaLowerSegment 470120704 470186240 (47009881640423 / 100000) (23508270565919 / 50000) := by
  exact
    packedTile32768 470120704 470186240 13 3335 21682 29 _ _ (1996849 / 100000) (499213 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470186240 :
    ThetaLowerSegment 470186240 470251776 (23508270565919 / 50000) (23511549413323 / 50000) := by
  exact
    packedTile32768 470186240 470251776 13 3284 21683 29 _ _ (998431 / 50000) (399373 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470251776 :
    ThetaLowerSegment 470251776 470317312 (23511549413323 / 50000) (4702955672363 / 10000) := by
  exact
    packedTile32768 470251776 470317312 13 3234 21685 29 _ _ (499219 / 25000) (1996879 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470317312 :
    ThetaLowerSegment 470317312 470382848 (4702955672363 / 10000) (4703613048551 / 10000) := by
  exact
    packedTile32768 470317312 470382848 13 3292 21686 29 _ _ (199689 / 10000) (1996893 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470382848 :
    ThetaLowerSegment 470382848 470448384 (4703613048551 / 10000) (4704266036159 / 10000) := by
  exact
    packedTile32768 470382848 470448384 13 3270 21688 29 _ _ (249613 / 12500) (1996907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470448384 :
    ThetaLowerSegment 470448384 470513920 (4704266036159 / 10000) (11762323031567 / 25000) := by
  exact
    packedTile32768 470448384 470513920 13 3321 21689 29 _ _ (998459 / 50000) (1996921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470513920 :
    ThetaLowerSegment 470513920 470579456 (11762323031567 / 25000) (5881981006753 / 12500) := by
  exact
    packedTile32768 470513920 470579456 13 3283 21691 29 _ _ (499233 / 25000) (399387 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470579456 :
    ThetaLowerSegment 470579456 470644992 (5881981006753 / 12500) (4706234012547 / 10000) := by
  exact
    packedTile32768 470579456 470644992 13 3251 21692 29 _ _ (998473 / 50000) (1996949 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470644992 :
    ThetaLowerSegment 470644992 470710528 (4706234012547 / 10000) (4706903792931 / 10000) := by
  exact
    packedTile32768 470644992 470710528 13 3354 21694 29 _ _ (12481 / 625) (1996963 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470710528 :
    ThetaLowerSegment 470710528 470776064 (4706903792931 / 10000) (23537762050431 / 50000) := by
  exact
    packedTile32768 470710528 470776064 13 3248 21695 29 _ _ (998487 / 50000) (1996977 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470776064 :
    ThetaLowerSegment 470776064 470841600 (23537762050431 / 50000) (23541041104727 / 50000) := by
  exact
    packedTile32768 470776064 470841600 13 3284 21697 29 _ _ (499247 / 25000) (1996991 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470841600 :
    ThetaLowerSegment 470841600 470907136 (23541041104727 / 50000) (5886073305621 / 12500) := by
  exact
    packedTile32768 470841600 470907136 13 3257 21698 29 _ _ (998501 / 50000) (399401 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470907136 :
    ThetaLowerSegment 470907136 470972672 (5886073305621 / 12500) (1471722334071 / 3125) := by
  exact
    packedTile32768 470907136 470972672 13 3269 21700 29 _ _ (249627 / 12500) (1997019 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell470972672 :
    ThetaLowerSegment 470972672 471038208 (1471722334071 / 3125) (23550871416421 / 50000) := by
  exact
    packedTile32768 470972672 471038208 13 3319 21701 29 _ _ (199703 / 10000) (1997033 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471038208 :
    ThetaLowerSegment 471038208 471103744 (23550871416421 / 50000) (47108227231463 / 100000) := by
  exact
    packedTile32768 471038208 471103744 13 3247 21703 29 _ _ (1997043 / 100000) (998523 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471103744 :
    ThetaLowerSegment 471103744 471169280 (47108227231463 / 100000) (942295990921 / 2000) := by
  exact
    packedTile32768 471103744 471169280 13 3291 21704 29 _ _ (1997057 / 100000) (99853 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471169280 :
    ThetaLowerSegment 471169280 471234816 (942295990921 / 2000) (11780336486197 / 25000) := by
  exact
    packedTile32768 471169280 471234816 13 3278 21706 29 _ _ (1997071 / 100000) (998537 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471234816 :
    ThetaLowerSegment 471234816 471300352 (11780336486197 / 25000) (23563986136409 / 50000) := by
  exact
    packedTile32768 471234816 471300352 13 3318 21707 29 _ _ (399417 / 20000) (62409 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471300352 :
    ThetaLowerSegment 471300352 471365888 (23563986136409 / 50000) (23567233419383 / 50000) := by
  exact
    packedTile32768 471300352 471365888 13 3252 21709 29 _ _ (1997099 / 100000) (998551 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471365888 :
    ThetaLowerSegment 471365888 471431424 (23567233419383 / 50000) (47141051320327 / 100000) := by
  exact
    packedTile32768 471365888 471431424 13 3297 21710 29 _ _ (1997113 / 100000) (499279 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471431424 :
    ThetaLowerSegment 471431424 471496960 (47141051320327 / 100000) (2357377997861 / 5000) := by
  exact
    packedTile32768 471431424 471496960 13 3259 21712 29 _ _ (1997127 / 100000) (199713 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471496960 :
    ThetaLowerSegment 471496960 471562496 (2357377997861 / 5000) (23577093235529 / 50000) := by
  exact
    packedTile32768 471496960 471562496 13 3318 21713 29 _ _ (1997141 / 100000) (249643 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471562496 :
    ThetaLowerSegment 471562496 471628032 (23577093235529 / 50000) (23580376558349 / 50000) := by
  exact
    packedTile32768 471562496 471628032 13 3288 21715 29 _ _ (399431 / 20000) (998579 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471628032 :
    ThetaLowerSegment 471628032 471693568 (23580376558349 / 50000) (5895896502233 / 12500) := by
  exact
    packedTile32768 471628032 471693568 13 3214 21716 29 _ _ (1997169 / 100000) (499293 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471693568 :
    ThetaLowerSegment 471693568 471759104 (5895896502233 / 12500) (1474180334703 / 3125) := by
  exact
    packedTile32768 471693568 471759104 13 3304 21718 29 _ _ (1997183 / 100000) (998593 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471759104 :
    ThetaLowerSegment 471759104 471824640 (1474180334703 / 3125) (11795077881849 / 25000) := by
  exact
    packedTile32768 471759104 471824640 13 3275 21720 29 _ _ (499299 / 25000) (1997199 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471824640 :
    ThetaLowerSegment 471824640 471890176 (11795077881849 / 25000) (23593506083473 / 50000) := by
  exact
    packedTile32768 471824640 471890176 13 3355 21721 29 _ _ (199721 / 10000) (1997213 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471890176 :
    ThetaLowerSegment 471890176 471955712 (23593506083473 / 50000) (23596794512789 / 50000) := by
  exact
    packedTile32768 471890176 471955712 13 3293 21723 29 _ _ (249653 / 12500) (1997227 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell471955712 :
    ThetaLowerSegment 471955712 472021248 (23596794512789 / 50000) (5900022738527 / 12500) := by
  exact
    packedTile32768 471955712 472021248 13 3301 21724 29 _ _ (998619 / 50000) (1997241 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472021248 :
    ThetaLowerSegment 472021248 472086784 (5900022738527 / 12500) (2360338342403 / 5000) := by
  exact
    packedTile32768 472021248 472086784 13 3297 21726 29 _ _ (499313 / 25000) (399451 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472086784 :
    ThetaLowerSegment 472086784 472152320 (2360338342403 / 5000) (23606625985381 / 50000) := by
  exact
    packedTile32768 472086784 472152320 13 3247 21727 29 _ _ (998633 / 50000) (1997269 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472152320 :
    ThetaLowerSegment 472152320 472217856 (23606625985381 / 50000) (23609895532741 / 50000) := by
  exact
    packedTile32768 472152320 472217856 13 3274 21729 29 _ _ (12483 / 625) (1997283 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472217856 :
    ThetaLowerSegment 472217856 472283392 (23609895532741 / 50000) (11806565075187 / 25000) := by
  exact
    packedTile32768 472217856 472283392 13 3239 21730 29 _ _ (998647 / 50000) (1997297 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472283392 :
    ThetaLowerSegment 472283392 472348928 (11806565075187 / 25000) (47232769524261 / 100000) := by
  exact
    packedTile32768 472283392 472348928 13 3259 21732 29 _ _ (1997307 / 100000) (199731 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472348928 :
    ThetaLowerSegment 472348928 472414464 (47232769524261 / 100000) (9447857756001 / 20000) := by
  exact
    packedTile32768 472348928 472414464 13 3264 21733 29 _ _ (1997321 / 100000) (499331 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472414464 :
    ThetaLowerSegment 472414464 472480000 (9447857756001 / 20000) (9449162415223 / 20000) := by
  exact
    packedTile32768 472414464 472480000 13 3266 21735 29 _ _ (399467 / 20000) (998669 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472480000 :
    ThetaLowerSegment 472480000 472545536 (9449162415223 / 20000) (236261667103 / 500) := by
  exact
    packedTile32768 472480000 472545536 13 3265 21736 29 _ _ (1997349 / 100000) (249669 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472545536 :
    ThetaLowerSegment 472545536 472611072 (236261667103 / 500) (23629464356613 / 50000) := by
  exact
    packedTile32768 472545536 472611072 13 3302 21738 29 _ _ (1997363 / 100000) (998683 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472611072 :
    ThetaLowerSegment 472611072 472676608 (23629464356613 / 50000) (23632776007679 / 50000) := by
  exact
    packedTile32768 472611072 472676608 13 3316 21739 29 _ _ (1997377 / 100000) (99869 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472676608 :
    ThetaLowerSegment 472676608 472742144 (23632776007679 / 50000) (23636015775881 / 50000) := by
  exact
    packedTile32768 472676608 472742144 13 3244 21741 29 _ _ (1997391 / 100000) (998697 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472742144 :
    ThetaLowerSegment 472742144 472807680 (23636015775881 / 50000) (47278469188077 / 100000) := by
  exact
    packedTile32768 472742144 472807680 13 3223 21742 29 _ _ (399481 / 20000) (62419 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472807680 :
    ThetaLowerSegment 472807680 472873216 (47278469188077 / 100000) (47285024713953 / 100000) := by
  exact
    packedTile32768 472807680 472873216 13 3282 21744 29 _ _ (998709 / 50000) (1997421 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472873216 :
    ThetaLowerSegment 472873216 472938752 (47285024713953 / 100000) (9458315657669 / 20000) := by
  exact
    packedTile32768 472873216 472938752 13 3281 21745 29 _ _ (249679 / 12500) (399487 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell472938752 :
    ThetaLowerSegment 472938752 473004288 (9458315657669 / 20000) (9459610002677 / 20000) := by
  exact
    packedTile32768 472938752 473004288 13 3240 21747 29 _ _ (998723 / 50000) (1997449 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473004288 :
    ThetaLowerSegment 473004288 473069824 (9459610002677 / 20000) (1892186783833 / 4000) := by
  exact
    packedTile32768 473004288 473069824 13 3314 21748 29 _ _ (99873 / 5000) (1997463 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473069824 :
    ThetaLowerSegment 473069824 473135360 (1892186783833 / 4000) (47311287227187 / 100000) := by
  exact
    packedTile32768 473069824 473135360 13 3313 21750 29 _ _ (998737 / 50000) (1997477 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473135360 :
    ThetaLowerSegment 473135360 473200896 (47311287227187 / 100000) (47317829000387 / 100000) := by
  exact
    packedTile32768 473135360 473200896 13 3275 21751 29 _ _ (124843 / 6250) (1997491 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473200896 :
    ThetaLowerSegment 473200896 473266432 (47317829000387 / 100000) (47324312891879 / 100000) := by
  exact
    packedTile32768 473200896 473266432 13 3246 21753 29 _ _ (998751 / 50000) (399501 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473266432 :
    ThetaLowerSegment 473266432 473331968 (47324312891879 / 100000) (2958176424579 / 6250) := by
  exact
    packedTile32768 473266432 473331968 13 3259 21754 29 _ _ (399503 / 20000) (998759 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473331968 :
    ThetaLowerSegment 473331968 473397504 (2958176424579 / 6250) (47337396661203 / 100000) := by
  exact
    packedTile32768 473331968 473397504 13 3291 21756 29 _ _ (1997529 / 100000) (499383 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473397504 :
    ThetaLowerSegment 473397504 473463040 (47337396661203 / 100000) (5918002314531 / 12500) := by
  exact
    packedTile32768 473397504 473463040 13 3315 21757 29 _ _ (1997543 / 100000) (998773 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473463040 :
    ThetaLowerSegment 473463040 473528576 (5918002314531 / 12500) (47350476618029 / 100000) := by
  exact
    packedTile32768 473463040 473528576 13 3233 21759 29 _ _ (1997557 / 100000) (49939 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473528576 :
    ThetaLowerSegment 473528576 473594112 (47350476618029 / 100000) (47357072597471 / 100000) := by
  exact
    packedTile32768 473528576 473594112 13 3302 21760 29 _ _ (1997571 / 100000) (998787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473594112 :
    ThetaLowerSegment 473594112 473659648 (47357072597471 / 100000) (47363580729401 / 100000) := by
  exact
    packedTile32768 473594112 473659648 13 3258 21762 29 _ _ (399517 / 20000) (499397 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473659648 :
    ThetaLowerSegment 473659648 473725184 (47363580729401 / 100000) (9474015783139 / 20000) := by
  exact
    packedTile32768 473659648 473725184 13 3253 21763 29 _ _ (998799 / 50000) (1997601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473725184 :
    ThetaLowerSegment 473725184 473790720 (9474015783139 / 20000) (47376615102159 / 100000) := by
  exact
    packedTile32768 473725184 473790720 13 3272 21765 29 _ _ (499403 / 25000) (399523 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473790720 :
    ThetaLowerSegment 473790720 473856256 (47376615102159 / 100000) (47383117374789 / 100000) := by
  exact
    packedTile32768 473790720 473856256 13 3255 21766 29 _ _ (998813 / 50000) (1997629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473856256 :
    ThetaLowerSegment 473856256 473921792 (47383117374789 / 100000) (47389607707149 / 100000) := by
  exact
    packedTile32768 473856256 473921792 13 3249 21768 29 _ _ (49941 / 2500) (1997643 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473921792 :
    ThetaLowerSegment 473921792 473987328 (47389607707149 / 100000) (47396299848049 / 100000) := by
  exact
    packedTile32768 473921792 473987328 13 3350 21769 29 _ _ (998827 / 50000) (1997657 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell473987328 :
    ThetaLowerSegment 473987328 474052864 (47396299848049 / 100000) (47402850201421 / 100000) := by
  exact
    packedTile32768 473987328 474052864 13 3279 21771 29 _ _ (499417 / 25000) (1997671 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474052864 :
    ThetaLowerSegment 474052864 474118400 (47402850201421 / 100000) (9481878121803 / 20000) := by
  exact
    packedTile32768 474052864 474118400 13 3274 21772 29 _ _ (1997681 / 100000) (499421 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474118400 :
    ThetaLowerSegment 474118400 474183936 (9481878121803 / 20000) (9483200595893 / 20000) := by
  exact
    packedTile32768 474118400 474183936 13 3310 21774 29 _ _ (399539 / 20000) (998849 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474183936 :
    ThetaLowerSegment 474183936 474249472 (9483200595893 / 20000) (47422539483313 / 100000) := by
  exact
    packedTile32768 474183936 474249472 13 3272 21775 29 _ _ (1997709 / 100000) (124857 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474249472 :
    ThetaLowerSegment 474249472 474315008 (47422539483313 / 100000) (47428984137711 / 100000) := by
  exact
    packedTile32768 474249472 474315008 13 3226 21777 29 _ _ (1997723 / 100000) (998863 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474315008 :
    ThetaLowerSegment 474315008 474380544 (47428984137711 / 100000) (47435612629077 / 100000) := by
  exact
    packedTile32768 474315008 474380544 13 3318 21778 29 _ _ (1997737 / 100000) (99887 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474380544 :
    ThetaLowerSegment 474380544 474446080 (47435612629077 / 100000) (23721029685777 / 50000) := by
  exact
    packedTile32768 474380544 474446080 13 3227 21780 29 _ _ (1997751 / 100000) (998877 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474446080 :
    ThetaLowerSegment 474446080 474511616 (23721029685777 / 50000) (23724271057867 / 50000) := by
  exact
    packedTile32768 474446080 474511616 13 3245 21781 29 _ _ (499441 / 25000) (1997767 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474511616 :
    ThetaLowerSegment 474511616 474577152 (23724271057867 / 50000) (23727527436007 / 50000) := by
  exact
    packedTile32768 474511616 474577152 13 3260 21783 29 _ _ (998889 / 50000) (1997781 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474577152 :
    ThetaLowerSegment 474577152 474642688 (23727527436007 / 50000) (23730830785079 / 50000) := by
  exact
    packedTile32768 474577152 474642688 13 3307 21784 29 _ _ (62431 / 3125) (399559 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474642688 :
    ThetaLowerSegment 474642688 474708224 (23730830785079 / 50000) (11867034114851 / 25000) := by
  exact
    packedTile32768 474642688 474708224 13 3241 21786 29 _ _ (998903 / 50000) (1997809 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474708224 :
    ThetaLowerSegment 474708224 474773760 (11867034114851 / 25000) (11868652349051 / 25000) := by
  exact
    packedTile32768 474708224 474773760 13 3240 21787 29 _ _ (99891 / 5000) (1997823 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474773760 :
    ThetaLowerSegment 474773760 474839296 (11868652349051 / 25000) (47481160290611 / 100000) := by
  exact
    packedTile32768 474773760 474839296 13 3279 21789 29 _ _ (1997833 / 100000) (499459 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474839296 :
    ThetaLowerSegment 474839296 474904832 (47481160290611 / 100000) (5935972894177 / 12500) := by
  exact
    packedTile32768 474839296 474904832 13 3315 21790 29 _ _ (1997847 / 100000) (39957 / 2000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474904832 :
    ThetaLowerSegment 474904832 474970368 (5935972894177 / 12500) (47494326148191 / 100000) := by
  exact
    packedTile32768 474904832 474970368 13 3275 21792 29 _ _ (1997861 / 100000) (249733 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell474970368 :
    ThetaLowerSegment 474970368 475035904 (47494326148191 / 100000) (47500891165441 / 100000) := by
  exact
    packedTile32768 474970368 475035904 13 3286 21793 29 _ _ (15983 / 800) (998939 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475035904 :
    ThetaLowerSegment 475035904 475101440 (47500891165441 / 100000) (23753711132291 / 50000) := by
  exact
    packedTile32768 475035904 475101440 13 3269 21795 29 _ _ (1997889 / 100000) (499473 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475101440 :
    ThetaLowerSegment 475101440 475166976 (23753711132291 / 50000) (23756967712551 / 50000) := by
  exact
    packedTile32768 475101440 475166976 13 3260 21796 29 _ _ (998951 / 50000) (399581 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475166976 :
    ThetaLowerSegment 475166976 475232512 (23756967712551 / 50000) (23760224315631 / 50000) := by
  exact
    packedTile32768 475166976 475232512 13 3260 21798 29 _ _ (499479 / 25000) (1997919 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475232512 :
    ThetaLowerSegment 475232512 475298048 (23760224315631 / 50000) (23763464958091 / 50000) := by
  exact
    packedTile32768 475232512 475298048 13 3244 21799 29 _ _ (199793 / 10000) (1997933 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475298048 :
    ThetaLowerSegment 475298048 475363584 (23763464958091 / 50000) (23766677652043 / 50000) := by
  exact
    packedTile32768 475298048 475363584 13 3216 21801 29 _ _ (249743 / 12500) (1997947 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475363584 :
    ThetaLowerSegment 475363584 475429120 (23766677652043 / 50000) (950799290983 / 2000) := by
  exact
    packedTile32768 475363584 475429120 13 3308 21802 29 _ _ (998979 / 50000) (1997961 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475429120 :
    ThetaLowerSegment 475429120 475494656 (950799290983 / 2000) (9509297584893 / 20000) := by
  exact
    packedTile32768 475429120 475494656 13 3265 21804 29 _ _ (1997971 / 100000) (998987 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475494656 :
    ThetaLowerSegment 475494656 475560192 (9509297584893 / 20000) (9510633837261 / 20000) := by
  exact
    packedTile32768 475494656 475560192 13 3344 21805 29 _ _ (399597 / 20000) (499497 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475560192 :
    ThetaLowerSegment 475560192 475625728 (9510633837261 / 20000) (1902388904921 / 4000) := by
  exact
    packedTile32768 475560192 475625728 13 3280 21807 29 _ _ (1997999 / 100000) (999001 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475625728 :
    ThetaLowerSegment 475625728 475691264 (1902388904921 / 4000) (11891588507043 / 25000) := by
  exact
    packedTile32768 475625728 475691264 13 3319 21808 29 _ _ (1998013 / 100000) (62438 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475691264 :
    ThetaLowerSegment 475691264 475756800 (11891588507043 / 25000) (11893206908103 / 25000) := by
  exact
    packedTile32768 475691264 475756800 13 3240 21810 29 _ _ (999013 / 50000) (1998029 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475756800 :
    ThetaLowerSegment 475756800 475822336 (11893206908103 / 25000) (11894860286203 / 25000) := by
  exact
    packedTile32768 475756800 475822336 13 3310 21811 29 _ _ (49951 / 2500) (1998043 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475822336 :
    ThetaLowerSegment 475822336 475887872 (11894860286203 / 25000) (23793096284639 / 50000) := by
  exact
    packedTile32768 475822336 475887872 13 3379 21813 29 _ _ (999027 / 50000) (1998057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475887872 :
    ThetaLowerSegment 475887872 475953408 (23793096284639 / 50000) (23796395094907 / 50000) := by
  exact
    packedTile32768 475887872 475953408 13 3302 21814 29 _ _ (499517 / 25000) (1998071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell475953408 :
    ThetaLowerSegment 475953408 476018944 (23796395094907 / 50000) (4759920003687 / 10000) := by
  exact
    packedTile32768 475953408 476018944 13 3208 21816 29 _ _ (999041 / 50000) (399617 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476018944 :
    ThetaLowerSegment 476018944 476084480 (4759920003687 / 10000) (1904227673901 / 4000) := by
  exact
    packedTile32768 476018944 476084480 13 3249 21817 29 _ _ (399619 / 20000) (999049 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476084480 :
    ThetaLowerSegment 476084480 476150016 (1904227673901 / 4000) (47612157728249 / 100000) := by
  exact
    packedTile32768 476084480 476150016 13 3236 21819 29 _ _ (1998109 / 100000) (62441 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476150016 :
    ThetaLowerSegment 476150016 476215552 (47612157728249 / 100000) (11904682388699 / 25000) := by
  exact
    packedTile32768 476150016 476215552 13 3289 21820 29 _ _ (1998123 / 100000) (999063 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476215552 :
    ThetaLowerSegment 476215552 476281088 (11904682388699 / 25000) (47625325405033 / 100000) := by
  exact
    packedTile32768 476215552 476281088 13 3301 21822 29 _ _ (1998137 / 100000) (99907 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476281088 :
    ThetaLowerSegment 476281088 476346624 (47625325405033 / 100000) (47631919300033 / 100000) := by
  exact
    packedTile32768 476281088 476346624 13 3300 21823 29 _ _ (39963 / 2000) (1998153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476346624 :
    ThetaLowerSegment 476346624 476412160 (47631919300033 / 100000) (47638487265101 / 100000) := by
  exact
    packedTile32768 476346624 476412160 13 3287 21825 29 _ _ (499541 / 25000) (1998167 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476412160 :
    ThetaLowerSegment 476412160 476477696 (47638487265101 / 100000) (47645019308983 / 100000) := by
  exact
    packedTile32768 476412160 476477696 13 3269 21826 29 _ _ (999089 / 50000) (1998181 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476477696 :
    ThetaLowerSegment 476477696 476543232 (47645019308983 / 100000) (47651581371511 / 100000) := by
  exact
    packedTile32768 476477696 476543232 13 3284 21828 29 _ _ (124887 / 6250) (399639 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476543232 :
    ThetaLowerSegment 476543232 476608768 (47651581371511 / 100000) (23829126689003 / 50000) := by
  exact
    packedTile32768 476543232 476608768 13 3339 21829 29 _ _ (399641 / 20000) (62444 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476608768 :
    ThetaLowerSegment 476608768 476674304 (23829126689003 / 50000) (47664753584413 / 100000) := by
  exact
    packedTile32768 476608768 476674304 13 3253 21831 29 _ _ (1998219 / 100000) (999111 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476674304 :
    ThetaLowerSegment 476674304 476739840 (47664753584413 / 100000) (11917830444071 / 25000) := by
  exact
    packedTile32768 476674304 476739840 13 3287 21832 29 _ _ (1998233 / 100000) (499559 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476739840 :
    ThetaLowerSegment 476739840 476805376 (11917830444071 / 25000) (47677850049233 / 100000) := by
  exact
    packedTile32768 476739840 476805376 13 3267 21834 29 _ _ (1998247 / 100000) (7993 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476805376 :
    ThetaLowerSegment 476805376 476870912 (47677850049233 / 100000) (47684462291573 / 100000) := by
  exact
    packedTile32768 476805376 476870912 13 3309 21835 29 _ _ (99913 / 5000) (1998263 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476870912 :
    ThetaLowerSegment 476870912 476936448 (47684462291573 / 100000) (9538202526749 / 20000) := by
  exact
    packedTile32768 476870912 476936448 13 3278 21837 29 _ _ (999137 / 50000) (1998277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell476936448 :
    ThetaLowerSegment 476936448 477001984 (9538202526749 / 20000) (47697565020097 / 100000) := by
  exact
    packedTile32768 476936448 477001984 13 3279 21838 29 _ _ (124893 / 6250) (1998291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477001984 :
    ThetaLowerSegment 477001984 477067520 (47697565020097 / 100000) (9540815497263 / 20000) := by
  exact
    packedTile32768 477001984 477067520 13 3259 21840 29 _ _ (999151 / 50000) (399661 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477067520 :
    ThetaLowerSegment 477067520 477133056 (9540815497263 / 20000) (9542133585837 / 20000) := by
  exact
    packedTile32768 477067520 477133056 13 3298 21841 29 _ _ (399663 / 20000) (999159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477133056 :
    ThetaLowerSegment 477133056 477198592 (9542133585837 / 20000) (23858612223317 / 50000) := by
  exact
    packedTile32768 477133056 477198592 13 3281 21843 29 _ _ (1998329 / 100000) (499583 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477198592 :
    ThetaLowerSegment 477198592 477264128 (23858612223317 / 50000) (47723745039843 / 100000) := by
  exact
    packedTile32768 477198592 477264128 13 3263 21844 29 _ _ (1998343 / 100000) (999173 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477264128 :
    ThetaLowerSegment 477264128 477329664 (47723745039843 / 100000) (47730295654089 / 100000) := by
  exact
    packedTile32768 477264128 477329664 13 3278 21846 29 _ _ (1998357 / 100000) (49959 / 2500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477329664 :
    ThetaLowerSegment 477329664 477395200 (47730295654089 / 100000) (47736882281609 / 100000) := by
  exact
    packedTile32768 477329664 477395200 13 3296 21847 29 _ _ (199837 / 10000) (1998373 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477395200 :
    ThetaLowerSegment 477395200 477460736 (47736882281609 / 100000) (47743436981129 / 100000) := by
  exact
    packedTile32768 477395200 477460736 13 3280 21849 29 _ _ (124899 / 6250) (1998387 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477460736 :
    ThetaLowerSegment 477460736 477526272 (47743436981129 / 100000) (47750049680111 / 100000) := by
  exact
    packedTile32768 477460736 477526272 13 3309 21850 29 _ _ (999199 / 50000) (1998401 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477526272 :
    ThetaLowerSegment 477526272 477591808 (47750049680111 / 100000) (23878347198343 / 50000) := by
  exact
    packedTile32768 477526272 477591808 13 3325 21852 29 _ _ (1998411 / 100000) (999207 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477591808 :
    ThetaLowerSegment 477591808 477657344 (23878347198343 / 50000) (47763235241711 / 100000) := by
  exact
    packedTile32768 477591808 477657344 13 3273 21853 29 _ _ (79937 / 4000) (499607 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477657344 :
    ThetaLowerSegment 477657344 477722880 (47763235241711 / 100000) (23884972000717 / 50000) := by
  exact
    packedTile32768 477657344 477722880 13 3357 21855 29 _ _ (1998439 / 100000) (999221 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477722880 :
    ThetaLowerSegment 477722880 477788416 (23884972000717 / 50000) (1911057319133 / 4000) := by
  exact
    packedTile32768 477722880 477788416 13 3247 21856 29 _ _ (1998453 / 100000) (249807 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477788416 :
    ThetaLowerSegment 477788416 477853952 (1911057319133 / 4000) (47782959968281 / 100000) := by
  exact
    packedTile32768 477788416 477853952 13 3266 21858 29 _ _ (999233 / 50000) (1998469 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477853952 :
    ThetaLowerSegment 477853952 477919488 (47782959968281 / 100000) (47789494997881 / 100000) := by
  exact
    packedTile32768 477853952 477919488 13 3270 21859 29 _ _ (24981 / 1250) (1998483 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477919488 :
    ThetaLowerSegment 477919488 477985024 (47789494997881 / 100000) (9559244385737 / 20000) := by
  exact
    packedTile32768 477919488 477985024 13 3366 21861 29 _ _ (999247 / 50000) (1998497 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell477985024 :
    ThetaLowerSegment 477985024 478050560 (9559244385737 / 20000) (47802828992827 / 100000) := by
  exact
    packedTile32768 477985024 478050560 13 3306 21862 29 _ _ (1998507 / 100000) (199851 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478050560 :
    ThetaLowerSegment 478050560 478116096 (47802828992827 / 100000) (9561884023017 / 20000) := by
  exact
    packedTile32768 478050560 478116096 13 3298 21864 29 _ _ (1998521 / 100000) (499631 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478116096 :
    ThetaLowerSegment 478116096 478181632 (9561884023017 / 20000) (956320265641 / 2000) := by
  exact
    packedTile32768 478116096 478181632 13 3299 21865 29 _ _ (399707 / 20000) (999269 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478181632 :
    ThetaLowerSegment 478181632 478247168 (956320265641 / 2000) (5977816568611 / 12500) := by
  exact
    packedTile32768 478181632 478247168 13 3262 21867 29 _ _ (1998549 / 100000) (249819 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478247168 :
    ThetaLowerSegment 478247168 478312704 (5977816568611 / 12500) (2989323485561 / 6250) := by
  exact
    packedTile32768 478247168 478312704 13 3324 21868 29 _ _ (999281 / 50000) (399713 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478312704 :
    ThetaLowerSegment 478312704 478378240 (2989323485561 / 6250) (2989733943107 / 6250) := by
  exact
    packedTile32768 478312704 478378240 13 3286 21870 29 _ _ (124911 / 6250) (1998579 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478378240 :
    ThetaLowerSegment 478378240 478443776 (2989733943107 / 6250) (1495067330201 / 3125) := by
  exact
    packedTile32768 478378240 478443776 13 3208 21871 29 _ _ (199859 / 10000) (1998593 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478443776 :
    ThetaLowerSegment 478443776 478509312 (1495067330201 / 3125) (47848664016403 / 100000) := by
  exact
    packedTile32768 478443776 478509312 13 3257 21873 29 _ _ (1998603 / 100000) (999303 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478509312 :
    ThetaLowerSegment 478509312 478574848 (47848664016403 / 100000) (957104829299 / 2000) := by
  exact
    packedTile32768 478509312 478574848 13 3291 21874 29 _ _ (1998617 / 100000) (99931 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478574848 :
    ThetaLowerSegment 478574848 478640384 (957104829299 / 2000) (23930874503743 / 50000) := by
  exact
    packedTile32768 478574848 478640384 13 3256 21876 29 _ _ (1998631 / 100000) (999317 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478640384 :
    ThetaLowerSegment 478640384 478705920 (23930874503743 / 50000) (47868318553601 / 100000) := by
  exact
    packedTile32768 478640384 478705920 13 3287 21877 29 _ _ (399729 / 20000) (249831 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478705920 :
    ThetaLowerSegment 478705920 478771456 (47868318553601 / 100000) (1914998803497 / 4000) := by
  exact
    packedTile32768 478705920 478771456 13 3328 21879 29 _ _ (999329 / 50000) (1998661 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478771456 :
    ThetaLowerSegment 478771456 478836992 (1914998803497 / 4000) (47881433792673 / 100000) := by
  exact
    packedTile32768 478771456 478836992 13 3234 21880 29 _ _ (124917 / 6250) (79947 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478836992 :
    ThetaLowerSegment 478836992 478902528 (47881433792673 / 100000) (47888007470927 / 100000) := by
  exact
    packedTile32768 478836992 478902528 13 3289 21882 29 _ _ (999343 / 50000) (1998689 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478902528 :
    ThetaLowerSegment 478902528 478968064 (47888007470927 / 100000) (11973652293431 / 25000) := by
  exact
    packedTile32768 478902528 478968064 13 3303 21883 29 _ _ (1998699 / 100000) (999351 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell478968064 :
    ThetaLowerSegment 478968064 479033600 (11973652293431 / 25000) (47901023043741 / 100000) := by
  exact
    packedTile32768 478968064 479033600 13 3209 21885 29 _ _ (1998713 / 100000) (499679 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479033600 :
    ThetaLowerSegment 479033600 479099136 (47901023043741 / 100000) (23953824411873 / 50000) := by
  exact
    packedTile32768 479033600 479099136 13 3315 21886 29 _ _ (1998727 / 100000) (199873 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479099136 :
    ThetaLowerSegment 479099136 479164672 (23953824411873 / 50000) (23957164306413 / 50000) := by
  exact
    packedTile32768 479099136 479164672 13 3342 21888 29 _ _ (99937 / 5000) (1998743 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479164672 :
    ThetaLowerSegment 479164672 479230208 (23957164306413 / 50000) (11980235622453 / 25000) := by
  exact
    packedTile32768 479164672 479230208 13 3309 21889 29 _ _ (999377 / 50000) (1998757 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479230208 :
    ThetaLowerSegment 479230208 479295744 (11980235622453 / 25000) (11981886604821 / 25000) := by
  exact
    packedTile32768 479230208 479295744 13 3304 21891 29 _ _ (124923 / 6250) (1998771 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479295744 :
    ThetaLowerSegment 479295744 479361280 (11981886604821 / 25000) (9586828879073 / 20000) := by
  exact
    packedTile32768 479295744 479361280 13 3301 21892 29 _ _ (1998781 / 100000) (62462 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479361280 :
    ThetaLowerSegment 479361280 479426816 (9586828879073 / 20000) (4794067445863 / 10000) := by
  exact
    packedTile32768 479361280 479426816 13 3267 21894 29 _ _ (399759 / 20000) (999399 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479426816 :
    ThetaLowerSegment 479426816 479492352 (4794067445863 / 10000) (11986830624341 / 25000) := by
  exact
    packedTile32768 479426816 479492352 13 3326 21895 29 _ _ (1998809 / 100000) (499703 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479492352 :
    ThetaLowerSegment 479492352 479557888 (11986830624341 / 25000) (2397688734739 / 5000) := by
  exact
    packedTile32768 479492352 479557888 13 3228 21897 29 _ _ (999411 / 50000) (79953 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479557888 :
    ThetaLowerSegment 479557888 479623424 (2397688734739 / 5000) (479604108303 / 1000) := by
  exact
    packedTile32768 479557888 479623424 13 3320 21898 29 _ _ (499709 / 25000) (1998839 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479623424 :
    ThetaLowerSegment 479623424 479688960 (479604108303 / 1000) (479669590629 / 1000) := by
  exact
    packedTile32768 479623424 479688960 13 3276 21900 29 _ _ (39977 / 2000) (1998853 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479688960 :
    ThetaLowerSegment 479688960 479754496 (479669590629 / 1000) (47973669245991 / 100000) := by
  exact
    packedTile32768 479688960 479754496 13 3357 21901 29 _ _ (1998863 / 100000) (999433 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479754496 :
    ThetaLowerSegment 479754496 479820032 (47973669245991 / 100000) (47980193580519 / 100000) := by
  exact
    packedTile32768 479754496 479820032 13 3264 21903 29 _ _ (1998877 / 100000) (12493 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479820032 :
    ThetaLowerSegment 479820032 479885568 (47980193580519 / 100000) (23993367975381 / 50000) := by
  exact
    packedTile32768 479820032 479885568 13 3273 21904 29 _ _ (1998891 / 100000) (999447 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479885568 :
    ThetaLowerSegment 479885568 479951104 (23993367975381 / 50000) (23996612196573 / 50000) := by
  exact
    packedTile32768 479885568 479951104 13 3246 21906 29 _ _ (249863 / 12500) (1998907 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell479951104 :
    ThetaLowerSegment 479951104 480016640 (23996612196573 / 50000) (5999969857011 / 12500) := by
  exact
    packedTile32768 479951104 480016640 13 3269 21907 29 _ _ (999459 / 50000) (1998921 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480016640 :
    ThetaLowerSegment 480016640 480082176 (5999969857011 / 12500) (300040295516 / 625) := by
  exact
    packedTile32768 480016640 480082176 13 3346 21909 29 _ _ (499733 / 25000) (399787 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480082176 :
    ThetaLowerSegment 480082176 480147712 (300040295516 / 625) (960260156401 / 2000) := by
  exact
    packedTile32768 480082176 480147712 13 3282 21910 29 _ _ (399789 / 20000) (499737 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480147712 :
    ThetaLowerSegment 480147712 480213248 (960260156401 / 2000) (48019526425349 / 100000) := by
  exact
    packedTile32768 480147712 480213248 13 3261 21912 29 _ _ (1998959 / 100000) (999481 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480213248 :
    ThetaLowerSegment 480213248 480278784 (48019526425349 / 100000) (12006542253157 / 25000) := by
  exact
    packedTile32768 480213248 480278784 13 3323 21913 29 _ _ (1998973 / 100000) (62468 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480278784 :
    ThetaLowerSegment 480278784 480344320 (12006542253157 / 25000) (4803255977087 / 10000) := by
  exact
    packedTile32768 480278784 480344320 13 3197 21915 29 _ _ (999493 / 50000) (1998989 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480344320 :
    ThetaLowerSegment 480344320 480409856 (4803255977087 / 10000) (4803910449687 / 10000) := by
  exact
    packedTile32768 480344320 480409856 13 3274 21916 29 _ _ (1999 / 100) (1999003 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480409856 :
    ThetaLowerSegment 480409856 480475392 (4803910449687 / 10000) (3002852704479 / 6250) := by
  exact
    packedTile32768 480409856 480475392 13 3271 21918 29 _ _ (999507 / 50000) (1999017 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480475392 :
    ThetaLowerSegment 480475392 480540928 (3002852704479 / 6250) (6006523011001 / 12500) := by
  exact
    packedTile32768 480475392 480540928 13 3272 21919 29 _ _ (1999027 / 100000) (199903 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480540928 :
    ThetaLowerSegment 480540928 480606464 (6006523011001 / 12500) (48058690966463 / 100000) := by
  exact
    packedTile32768 480540928 480606464 13 3255 21921 29 _ _ (1999041 / 100000) (499761 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480606464 :
    ThetaLowerSegment 480606464 480672000 (48058690966463 / 100000) (48065227873043 / 100000) := by
  exact
    packedTile32768 480606464 480672000 13 3270 21922 29 _ _ (999527 / 50000) (1999057 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480672000 :
    ThetaLowerSegment 480672000 480737536 (48065227873043 / 100000) (48071708851499 / 100000) := by
  exact
    packedTile32768 480672000 480737536 13 3242 21924 29 _ _ (499767 / 25000) (1999071 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480737536 :
    ThetaLowerSegment 480737536 480803072 (48071708851499 / 100000) (48078263841377 / 100000) := by
  exact
    packedTile32768 480737536 480803072 13 3279 21925 29 _ _ (999541 / 50000) (399817 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480803072 :
    ThetaLowerSegment 480803072 480868608 (48078263841377 / 100000) (24042477406171 / 50000) := by
  exact
    packedTile32768 480803072 480868608 13 3347 21927 29 _ _ (399819 / 20000) (999549 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480868608 :
    ThetaLowerSegment 480868608 480934144 (24042477406171 / 50000) (48091501894317 / 100000) := by
  exact
    packedTile32768 480868608 480934144 13 3275 21928 29 _ _ (1999109 / 100000) (249889 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480934144 :
    ThetaLowerSegment 480934144 480999680 (48091501894317 / 100000) (24049004519841 / 50000) := by
  exact
    packedTile32768 480934144 480999680 13 3255 21930 29 _ _ (1999123 / 100000) (999563 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell480999680 :
    ThetaLowerSegment 480999680 481065216 (24049004519841 / 50000) (4810460219021 / 10000) := by
  exact
    packedTile32768 480999680 481065216 13 3298 21931 29 _ _ (62473 / 3125) (1999139 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481065216 :
    ThetaLowerSegment 481065216 481130752 (4810460219021 / 10000) (4811114340901 / 10000) := by
  exact
    packedTile32768 481065216 481130752 13 3272 21933 29 _ _ (39983 / 2000) (1999153 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481130752 :
    ThetaLowerSegment 481130752 481196288 (4811114340901 / 10000) (300734754514 / 625) := by
  exact
    packedTile32768 481130752 481196288 13 3210 21934 29 _ _ (1999163 / 100000) (999583 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481196288 :
    ThetaLowerSegment 481196288 481261824 (300734754514 / 625) (12031051496647 / 25000) := by
  exact
    packedTile32768 481196288 481261824 13 3324 21936 29 _ _ (1999177 / 100000) (99959 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481261824 :
    ThetaLowerSegment 481261824 481327360 (12031051496647 / 25000) (48130809314461 / 100000) := by
  exact
    packedTile32768 481261824 481327360 13 3303 21937 29 _ _ (1999191 / 100000) (999597 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481327360 :
    ThetaLowerSegment 481327360 481392896 (48130809314461 / 100000) (48137312725073 / 100000) := by
  exact
    packedTile32768 481327360 481392896 13 3253 21939 29 _ _ (499801 / 25000) (1999207 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481392896 :
    ThetaLowerSegment 481392896 481458432 (48137312725073 / 100000) (48143814182009 / 100000) := by
  exact
    packedTile32768 481392896 481458432 13 3252 21940 29 _ _ (999609 / 50000) (1999221 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481458432 :
    ThetaLowerSegment 481458432 481523968 (48143814182009 / 100000) (48150545596153 / 100000) := by
  exact
    packedTile32768 481458432 481523968 13 3367 21942 29 _ _ (62476 / 3125) (399847 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481523968 :
    ThetaLowerSegment 481523968 481589504 (48150545596153 / 100000) (48157091124283 / 100000) := by
  exact
    packedTile32768 481523968 481589504 13 3274 21943 29 _ _ (399849 / 20000) (124953 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481589504 :
    ThetaLowerSegment 481589504 481655040 (48157091124283 / 100000) (48163512744191 / 100000) := by
  exact
    packedTile32768 481589504 481655040 13 3212 21945 29 _ _ (1999259 / 100000) (999631 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481655040 :
    ThetaLowerSegment 481655040 481720576 (48163512744191 / 100000) (48170160323591 / 100000) := by
  exact
    packedTile32768 481655040 481720576 13 3325 21946 29 _ _ (249909 / 12500) (79971 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481720576 :
    ThetaLowerSegment 481720576 481786112 (48170160323591 / 100000) (48176721980243 / 100000) := by
  exact
    packedTile32768 481720576 481786112 13 3282 21948 29 _ _ (999643 / 50000) (1999289 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481786112 :
    ThetaLowerSegment 481786112 481851648 (48176721980243 / 100000) (48183157726943 / 100000) := by
  exact
    packedTile32768 481786112 481851648 13 3219 21949 29 _ _ (19993 / 1000) (1999303 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481851648 :
    ThetaLowerSegment 481851648 481917184 (48183157726943 / 100000) (48189639499689 / 100000) := by
  exact
    packedTile32768 481851648 481917184 13 3242 21951 29 _ _ (1999313 / 100000) (499829 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481917184 :
    ThetaLowerSegment 481917184 481982720 (48189639499689 / 100000) (9639230661411 / 20000) := by
  exact
    packedTile32768 481917184 481982720 13 3258 21952 29 _ _ (1999327 / 100000) (199933 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell481982720 :
    ThetaLowerSegment 481982720 482048256 (9639230661411 / 20000) (9640545027527 / 20000) := by
  exact
    packedTile32768 481982720 482048256 13 3287 21954 29 _ _ (99967 / 5000) (1999343 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482048256 :
    ThetaLowerSegment 482048256 482113792 (9640545027527 / 20000) (48209378987747 / 100000) := by
  exact
    packedTile32768 482048256 482113792 13 3328 21955 29 _ _ (999677 / 50000) (1999357 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482113792 :
    ThetaLowerSegment 482113792 482179328 (48209378987747 / 100000) (48215916921107 / 100000) := by
  exact
    packedTile32768 482113792 482179328 13 3270 21957 29 _ _ (249921 / 12500) (1999371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482179328 :
    ThetaLowerSegment 482179328 482244864 (48215916921107 / 100000) (24111228448179 / 50000) := by
  exact
    packedTile32768 482179328 482244864 13 3271 21958 29 _ _ (1999381 / 100000) (249923 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482244864 :
    ThetaLowerSegment 482244864 482310400 (24111228448179 / 50000) (48229036905303 / 100000) := by
  exact
    packedTile32768 482244864 482310400 13 3291 21960 29 _ _ (399879 / 20000) (999699 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482310400 :
    ThetaLowerSegment 482310400 482375936 (48229036905303 / 100000) (9647096599339 / 20000) := by
  exact
    packedTile32768 482310400 482375936 13 3224 21961 29 _ _ (124963 / 6250) (1999411 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482375936 :
    ThetaLowerSegment 482375936 482441472 (9647096599339 / 20000) (48242049098543 / 100000) := by
  exact
    packedTile32768 482375936 482441472 13 3284 21963 29 _ _ (999711 / 50000) (79977 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482441472 :
    ThetaLowerSegment 482441472 482507008 (48242049098543 / 100000) (9649726248371 / 20000) := by
  exact
    packedTile32768 482441472 482507008 13 3292 21964 29 _ _ (499859 / 25000) (1999439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482507008 :
    ThetaLowerSegment 482507008 482572544 (9649726248371 / 20000) (12063791860159 / 25000) := by
  exact
    packedTile32768 482507008 482572544 13 3269 21966 29 _ _ (1999449 / 100000) (499863 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482572544 :
    ThetaLowerSegment 482572544 482638080 (12063791860159 / 25000) (24130892831583 / 50000) := by
  exact
    packedTile32768 482572544 482638080 13 3310 21967 29 _ _ (1999463 / 100000) (999733 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482638080 :
    ThetaLowerSegment 482638080 482703616 (24130892831583 / 50000) (24134114987157 / 50000) := by
  exact
    packedTile32768 482638080 482703616 13 3223 21969 29 _ _ (499869 / 25000) (1999479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482703616 :
    ThetaLowerSegment 482703616 482769152 (24134114987157 / 50000) (24137400149227 / 50000) := by
  exact
    packedTile32768 482703616 482769152 13 3286 21970 29 _ _ (199949 / 10000) (1999493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482769152 :
    ThetaLowerSegment 482769152 482834688 (24137400149227 / 50000) (48281388660839 / 100000) := by
  exact
    packedTile32768 482769152 482834688 13 3295 21972 29 _ _ (1999503 / 100000) (999753 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482834688 :
    ThetaLowerSegment 482834688 482900224 (48281388660839 / 100000) (1207197327241 / 2500) := by
  exact
    packedTile32768 482834688 482900224 13 3253 21973 29 _ _ (1999517 / 100000) (12497 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482900224 :
    ThetaLowerSegment 482900224 482965760 (1207197327241 / 2500) (3018404221723 / 6250) := by
  exact
    packedTile32768 482900224 482965760 13 3288 21974 29 _ _ (1999531 / 100000) (999767 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell482965760 :
    ThetaLowerSegment 482965760 483031296 (3018404221723 / 6250) (1509406439264 / 3125) := by
  exact
    packedTile32768 482965760 483031296 13 3270 21976 29 _ _ (249943 / 12500) (1999547 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483031296 :
    ThetaLowerSegment 483031296 483096832 (1509406439264 / 3125) (24153813296493 / 50000) := by
  exact
    packedTile32768 483031296 483096832 13 3311 21977 29 _ _ (999779 / 50000) (1999561 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483096832 :
    ThetaLowerSegment 483096832 483162368 (24153813296493 / 50000) (24157080595507 / 50000) := by
  exact
    packedTile32768 483096832 483162368 13 3268 21979 29 _ _ (1999571 / 100000) (999787 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483162368 :
    ThetaLowerSegment 483162368 483227904 (24157080595507 / 50000) (12080198953511 / 25000) := by
  exact
    packedTile32768 483162368 483227904 13 3318 21980 29 _ _ (399917 / 20000) (499897 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483227904 :
    ThetaLowerSegment 483227904 483293440 (12080198953511 / 25000) (24163690245129 / 50000) := by
  exact
    packedTile32768 483227904 483293440 13 3293 21982 29 _ _ (999799 / 50000) (1999601 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483293440 :
    ThetaLowerSegment 483293440 483358976 (24163690245129 / 50000) (24166937615017 / 50000) := by
  exact
    packedTile32768 483293440 483358976 13 3248 21983 29 _ _ (499903 / 25000) (399923 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483358976 :
    ThetaLowerSegment 483358976 483424512 (24166937615017 / 50000) (6042556000087 / 12500) := by
  exact
    packedTile32768 483358976 483424512 13 3287 21985 29 _ _ (999813 / 50000) (1999629 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483424512 :
    ThetaLowerSegment 483424512 483490048 (6042556000087 / 12500) (24173493410113 / 50000) := by
  exact
    packedTile32768 483424512 483490048 13 3270 21986 29 _ _ (1999639 / 100000) (999821 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483490048 :
    ThetaLowerSegment 483490048 483555584 (24173493410113 / 50000) (24176804835481 / 50000) := by
  exact
    packedTile32768 483490048 483555584 13 3312 21988 29 _ _ (1999653 / 100000) (249957 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483555584 :
    ThetaLowerSegment 483555584 483621120 (24176804835481 / 50000) (12090030645781 / 25000) := by
  exact
    packedTile32768 483555584 483621120 13 3257 21989 29 _ _ (999833 / 50000) (1999669 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483621120 :
    ThetaLowerSegment 483621120 483686656 (12090030645781 / 25000) (12091667383861 / 25000) := by
  exact
    packedTile32768 483621120 483686656 13 3274 21991 29 _ _ (12498 / 625) (1999683 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483686656 :
    ThetaLowerSegment 483686656 483752192 (12091667383861 / 25000) (48373278520809 / 100000) := by
  exact
    packedTile32768 483686656 483752192 13 3305 21992 29 _ _ (1999693 / 100000) (124981 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483752192 :
    ThetaLowerSegment 483752192 483817728 (48373278520809 / 100000) (48379801565043 / 100000) := by
  exact
    packedTile32768 483752192 483817728 13 3262 21994 29 _ _ (1999707 / 100000) (199971 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483817728 :
    ThetaLowerSegment 483817728 483883264 (48379801565043 / 100000) (48386222665963 / 100000) := by
  exact
    packedTile32768 483817728 483883264 13 3211 21995 29 _ _ (49993 / 2500) (1999723 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483883264 :
    ThetaLowerSegment 483883264 483948800 (48386222665963 / 100000) (48392679807049 / 100000) := by
  exact
    packedTile32768 483883264 483948800 13 3229 21997 29 _ _ (999867 / 50000) (1999737 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell483948800 :
    ThetaLowerSegment 483948800 484014336 (48392679807049 / 100000) (4839932496633 / 10000) := by
  exact
    packedTile32768 483948800 484014336 13 3323 21998 29 _ _ (1999747 / 100000) (7999 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484014336 :
    ThetaLowerSegment 484014336 484079872 (4839932496633 / 10000) (48405926177391 / 100000) := by
  exact
    packedTile32768 484014336 484079872 13 3301 22000 29 _ _ (1999761 / 100000) (499941 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484079872 :
    ThetaLowerSegment 484079872 484145408 (48405926177391 / 100000) (48412561430841 / 100000) := by
  exact
    packedTile32768 484079872 484145408 13 3318 22001 29 _ _ (79991 / 4000) (999889 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484145408 :
    ThetaLowerSegment 484145408 484210944 (48412561430841 / 100000) (48419102737389 / 100000) := by
  exact
    packedTile32768 484145408 484210944 13 3271 22003 29 _ _ (499947 / 25000) (1999791 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484210944 :
    ThetaLowerSegment 484210944 484276480 (48419102737389 / 100000) (48425694084781 / 100000) := by
  exact
    packedTile32768 484210944 484276480 13 3296 22004 29 _ _ (999901 / 50000) (399961 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484276480 :
    ThetaLowerSegment 484276480 484342016 (48425694084781 / 100000) (12108071868709 / 25000) := by
  exact
    packedTile32768 484276480 484342016 13 3297 22006 29 _ _ (399963 / 20000) (999909 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484342016 :
    ThetaLowerSegment 484342016 484407552 (12108071868709 / 25000) (12109711728489 / 25000) := by
  exact
    packedTile32768 484342016 484407552 13 3280 22007 29 _ _ (1999829 / 100000) (249979 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484407552 :
    ThetaLowerSegment 484407552 484473088 (12109711728489 / 25000) (12111331600509 / 25000) := by
  exact
    packedTile32768 484407552 484473088 13 3240 22009 29 _ _ (999921 / 50000) (399969 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484473088 :
    ThetaLowerSegment 484473088 484538624 (12111331600509 / 25000) (12112981481709 / 25000) := by
  exact
    packedTile32768 484473088 484538624 13 3300 22010 29 _ _ (124991 / 6250) (1999859 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484538624 :
    ThetaLowerSegment 484538624 484604160 (12112981481709 / 25000) (48458543493357 / 100000) := by
  exact
    packedTile32768 484538624 484604160 13 3309 22012 29 _ _ (1999869 / 100000) (62496 / 3125)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484604160 :
    ThetaLowerSegment 484604160 484669696 (48458543493357 / 100000) (48464999115681 / 100000) := by
  exact
    packedTile32768 484604160 484669696 13 3228 22013 29 _ _ (1999883 / 100000) (999943 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484669696 :
    ThetaLowerSegment 484669696 484735232 (48464999115681 / 100000) (48471500777577 / 100000) := by
  exact
    packedTile32768 484669696 484735232 13 3251 22015 29 _ _ (249987 / 12500) (1999899 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484735232 :
    ThetaLowerSegment 484735232 484800768 (48471500777577 / 100000) (48478170477427 / 100000) := by
  exact
    packedTile32768 484735232 484800768 13 3335 22016 29 _ _ (199991 / 10000) (1999913 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484800768 :
    ThetaLowerSegment 484800768 484866304 (48478170477427 / 100000) (48484738224559 / 100000) := by
  exact
    packedTile32768 484800768 484866304 13 3284 22018 29 _ _ (1999923 / 100000) (999963 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484866304 :
    ThetaLowerSegment 484866304 484931840 (48484738224559 / 100000) (24245576011259 / 50000) := by
  exact
    packedTile32768 484866304 484931840 13 3207 22019 29 _ _ (1999937 / 100000) (99997 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484931840 :
    ThetaLowerSegment 484931840 484997376 (24245576011259 / 50000) (6062215732271 / 12500) := by
  exact
    packedTile32768 484931840 484997376 13 3287 22021 29 _ _ (39999 / 2000) (1999953 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell484997376 :
    ThetaLowerSegment 484997376 485062912 (6062215732271 / 12500) (3031503109021 / 6250) := by
  exact
    packedTile32768 484997376 485062912 13 3162 22022 29 _ _ (499991 / 25000) (1999967 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485062912 :
    ThetaLowerSegment 485062912 485128448 (3031503109021 / 6250) (24255278834747 / 50000) := by
  exact
    packedTile32768 485062912 485128448 13 3254 22024 29 _ _ (1999977 / 100000) (99999 / 5000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485128448 :
    ThetaLowerSegment 485128448 485193984 (24255278834747 / 50000) (970343792793 / 2000) := by
  exact
    packedTile32768 485128448 485193984 13 3316 22025 29 _ _ (1999991 / 100000) (999997 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485193984 :
    ThetaLowerSegment 485193984 485259520 (970343792793 / 2000) (24261962826561 / 50000) := by
  exact
    packedTile32768 485193984 485259520 13 3368 22027 29 _ _ (500001 / 25000) (2000007 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485259520 :
    ThetaLowerSegment 485259520 485325056 (24261962826561 / 50000) (24265196855667 / 50000) := by
  exact
    packedTile32768 485259520 485325056 13 3234 22028 29 _ _ (1000009 / 50000) (2000021 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485325056 :
    ThetaLowerSegment 485325056 485390592 (24265196855667 / 50000) (48537027814161 / 100000) := by
  exact
    packedTile32768 485325056 485390592 13 3317 22030 29 _ _ (2000031 / 100000) (1000017 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485390592 :
    ThetaLowerSegment 485390592 485456128 (48537027814161 / 100000) (6067945245147 / 12500) := by
  exact
    packedTile32768 485390592 485456128 13 3267 22031 29 _ _ (400009 / 20000) (125003 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485456128 :
    ThetaLowerSegment 485456128 485521664 (6067945245147 / 12500) (24275046075273 / 50000) := by
  exact
    packedTile32768 485456128 485521664 13 3265 22033 29 _ _ (1000029 / 50000) (2000061 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485521664 :
    ThetaLowerSegment 485521664 485587200 (24275046075273 / 50000) (24278329193461 / 50000) := by
  exact
    packedTile32768 485521664 485587200 13 3283 22034 29 _ _ (250009 / 12500) (80003 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485587200 :
    ThetaLowerSegment 485587200 485652736 (24278329193461 / 50000) (24281617333201 / 50000) := by
  exact
    packedTile32768 485587200 485652736 13 3288 22036 29 _ _ (400017 / 20000) (250011 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485652736 :
    ThetaLowerSegment 485652736 485718272 (24281617333201 / 50000) (48569800991419 / 100000) := by
  exact
    packedTile32768 485652736 485718272 13 3283 22037 29 _ _ (2000099 / 100000) (1000051 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485718272 :
    ThetaLowerSegment 485718272 485783808 (48569800991419 / 100000) (48576299355307 / 100000) := by
  exact
    packedTile32768 485718272 485783808 13 3249 22039 29 _ _ (125007 / 6250) (400023 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485783808 :
    ThetaLowerSegment 485783808 485849344 (48576299355307 / 100000) (48582939773627 / 100000) := by
  exact
    packedTile32768 485783808 485849344 13 3320 22040 29 _ _ (1000063 / 50000) (2000129 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485849344 :
    ThetaLowerSegment 485849344 485914880 (48582939773627 / 100000) (9717904846243 / 20000) := by
  exact
    packedTile32768 485849344 485914880 13 3292 22041 29 _ _ (2000139 / 100000) (1000071 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485914880 :
    ThetaLowerSegment 485914880 485980416 (9717904846243 / 20000) (48596028728771 / 100000) := by
  exact
    packedTile32768 485914880 485980416 13 3252 22043 29 _ _ (2000153 / 100000) (500039 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell485980416 :
    ThetaLowerSegment 485980416 486045952 (48596028728771 / 100000) (9720535456111 / 20000) := by
  exact
    packedTile32768 485980416 486045952 13 3324 22044 29 _ _ (1000083 / 50000) (2000169 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486045952 :
    ThetaLowerSegment 486045952 486111488 (9720535456111 / 20000) (9721831972787 / 20000) := by
  exact
    packedTile32768 486045952 486111488 13 3241 22046 29 _ _ (100009 / 5000) (2000183 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486111488 :
    ThetaLowerSegment 486111488 486177024 (9721831972787 / 20000) (48615736498519 / 100000) := by
  exact
    packedTile32768 486111488 486177024 13 3288 22047 29 _ _ (2000193 / 100000) (500049 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486177024 :
    ThetaLowerSegment 486177024 486242560 (48615736498519 / 100000) (48622281175823 / 100000) := by
  exact
    packedTile32768 486177024 486242560 13 3272 22049 29 _ _ (2000207 / 100000) (200021 / 10000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486242560 :
    ThetaLowerSegment 486242560 486308096 (48622281175823 / 100000) (48628769889503 / 100000) := by
  exact
    packedTile32768 486242560 486308096 13 3244 22050 29 _ _ (100011 / 5000) (2000223 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486308096 :
    ThetaLowerSegment 486308096 486373632 (48628769889503 / 100000) (48635300653513 / 100000) := by
  exact
    packedTile32768 486308096 486373632 13 3265 22052 29 _ _ (1000117 / 50000) (2000237 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486373632 :
    ThetaLowerSegment 486373632 486439168 (48635300653513 / 100000) (48641889467131 / 100000) := by
  exact
    packedTile32768 486373632 486439168 13 3294 22053 29 _ _ (2000247 / 100000) (8001 / 400)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486439168 :
    ThetaLowerSegment 486439168 486504704 (48641889467131 / 100000) (48648470325821 / 100000) := by
  exact
    packedTile32768 486439168 486504704 13 3290 22055 29 _ _ (2000261 / 100000) (250033 / 12500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486504704 :
    ThetaLowerSegment 486504704 486570240 (48648470325821 / 100000) (48655039225637 / 100000) := by
  exact
    packedTile32768 486504704 486570240 13 3284 22056 29 _ _ (1000137 / 50000) (2000277 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486570240 :
    ThetaLowerSegment 486570240 486635776 (48655039225637 / 100000) (48661588168549 / 100000) := by
  exact
    packedTile32768 486570240 486635776 13 3274 22058 29 _ _ (62509 / 3125) (2000291 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486635776 :
    ThetaLowerSegment 486635776 486701312 (48661588168549 / 100000) (9733636232129 / 20000) := by
  exact
    packedTile32768 486635776 486701312 13 3296 22059 29 _ _ (2000301 / 100000) (125019 / 6250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486701312 :
    ThetaLowerSegment 486701312 486766848 (9733636232129 / 20000) (243374281059 / 500) := by
  exact
    packedTile32768 486701312 486766848 13 3337 22061 29 _ _ (400063 / 20000) (1000159 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486766848 :
    ThetaLowerSegment 486766848 486832384 (243374281059 / 500) (6085163658741 / 12500) := by
  exact
    packedTile32768 486766848 486832384 13 3226 22062 29 _ _ (250041 / 12500) (2000331 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486832384 :
    ThetaLowerSegment 486832384 486897920 (6085163658741 / 12500) (12171954595699 / 25000) := by
  exact
    packedTile32768 486832384 486897920 13 3254 22064 29 _ _ (1000171 / 50000) (400069 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486897920 :
    ThetaLowerSegment 486897920 486963456 (12171954595699 / 25000) (12173590886089 / 25000) := by
  exact
    packedTile32768 486897920 486963456 13 3272 22065 29 _ _ (400071 / 20000) (1000179 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell486963456 :
    ThetaLowerSegment 486963456 487028992 (12173590886089 / 25000) (12175207183433 / 25000) := by
  exact
    packedTile32768 486963456 487028992 13 3232 22067 29 _ _ (125023 / 6250) (2000371 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487028992 :
    ThetaLowerSegment 487028992 487094528 (12175207183433 / 25000) (194828911823 / 400) := by
  exact
    packedTile32768 487028992 487094528 13 3199 22068 29 _ _ (1000191 / 50000) (400077 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487094528 :
    ThetaLowerSegment 487094528 487160064 (194828911823 / 400) (2435688062291 / 5000) := by
  exact
    packedTile32768 487094528 487160064 13 3266 22070 29 _ _ (400079 / 20000) (1000199 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487160064 :
    ThetaLowerSegment 487160064 487225600 (2435688062291 / 5000) (48720324587749 / 100000) := by
  exact
    packedTile32768 487160064 487225600 13 3281 22071 29 _ _ (2000409 / 100000) (500103 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487225600 :
    ThetaLowerSegment 487225600 487291136 (48720324587749 / 100000) (48726975990899 / 100000) := by
  exact
    packedTile32768 487225600 487291136 13 3325 22073 29 _ _ (1000211 / 50000) (80017 / 4000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487291136 :
    ThetaLowerSegment 487291136 487356672 (48726975990899 / 100000) (48733527418799 / 100000) := by
  exact
    packedTile32768 487291136 487356672 13 3275 22074 29 _ _ (500109 / 25000) (2000439 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487356672 :
    ThetaLowerSegment 487356672 487422208 (48733527418799 / 100000) (24370047446433 / 50000) := by
  exact
    packedTile32768 487356672 487422208 13 3283 22076 29 _ _ (2000449 / 100000) (500113 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487422208 :
    ThetaLowerSegment 487422208 487487744 (24370047446433 / 50000) (9749332482579 / 20000) := by
  exact
    packedTile32768 487422208 487487744 13 3283 22077 29 _ _ (2000463 / 100000) (1000233 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487487744 :
    ThetaLowerSegment 487487744 487553280 (9749332482579 / 20000) (48753235977031 / 100000) := by
  exact
    packedTile32768 487487744 487553280 13 3286 22079 29 _ _ (500119 / 25000) (2000479 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487553280 :
    ThetaLowerSegment 487553280 487618816 (48753235977031 / 100000) (48759783580801 / 100000) := by
  exact
    packedTile32768 487553280 487618816 13 3273 22080 29 _ _ (200049 / 10000) (2000493 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487618816 :
    ThetaLowerSegment 487618816 487684352 (48759783580801 / 100000) (48766377238689 / 100000) := by
  exact
    packedTile32768 487618816 487684352 13 3296 22082 29 _ _ (2000503 / 100000) (1000253 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487684352 :
    ThetaLowerSegment 487684352 487749888 (48766377238689 / 100000) (48772902921881 / 100000) := by
  exact
    packedTile32768 487684352 487749888 13 3262 22083 29 _ _ (500129 / 25000) (2000519 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487749888 :
    ThetaLowerSegment 487749888 487815424 (48772902921881 / 100000) (48779594694731 / 100000) := by
  exact
    packedTile32768 487749888 487815424 13 3345 22085 29 _ _ (200053 / 10000) (2000533 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487815424 :
    ThetaLowerSegment 487815424 487880960 (48779594694731 / 100000) (48786136470341 / 100000) := by
  exact
    packedTile32768 487815424 487880960 13 3270 22086 29 _ _ (2000543 / 100000) (1000273 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487880960 :
    ThetaLowerSegment 487880960 487946496 (48786136470341 / 100000) (48792746310669 / 100000) := by
  exact
    packedTile32768 487880960 487946496 13 3304 22088 29 _ _ (2000557 / 100000) (25007 / 1250)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell487946496 :
    ThetaLowerSegment 487946496 488012032 (48792746310669 / 100000) (48799204150629 / 100000) := by
  exact
    packedTile32768 487946496 488012032 13 3228 22089 29 _ _ (200057 / 10000) (2000573 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488012032 :
    ThetaLowerSegment 488012032 488077568 (48799204150629 / 100000) (9761136808441 / 20000) := by
  exact
    packedTile32768 488012032 488077568 13 3239 22090 29 _ _ (250073 / 12500) (2000587 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488077568 :
    ThetaLowerSegment 488077568 488143104 (9761136808441 / 20000) (48812157974097 / 100000) := by
  exact
    packedTile32768 488077568 488143104 13 3236 22092 29 _ _ (2000597 / 100000) (10003 / 500)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488143104 :
    ThetaLowerSegment 488143104 488208640 (48812157974097 / 100000) (48818721975507 / 100000) := by
  exact
    packedTile32768 488143104 488208640 13 3281 22093 29 _ _ (200061 / 10000) (2000613 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488208640 :
    ThetaLowerSegment 488208640 488274176 (48818721975507 / 100000) (48825360045939 / 100000) := by
  exact
    packedTile32768 488208640 488274176 13 3318 22095 29 _ _ (125039 / 6250) (2000627 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488274176 :
    ThetaLowerSegment 488274176 488339712 (48825360045939 / 100000) (48831894126381 / 100000) := by
  exact
    packedTile32768 488274176 488339712 13 3266 22096 29 _ _ (2000637 / 100000) (12504 / 625)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488339712 :
    ThetaLowerSegment 488339712 488405248 (48831894126381 / 100000) (48838316216091 / 100000) := by
  exact
    packedTile32768 488339712 488405248 13 3210 22098 29 _ _ (2000651 / 100000) (1000327 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488405248 :
    ThetaLowerSegment 488405248 488470784 (48838316216091 / 100000) (48844842382059 / 100000) := by
  exact
    packedTile32768 488405248 488470784 13 3262 22099 29 _ _ (250083 / 12500) (2000667 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488470784 :
    ThetaLowerSegment 488470784 488536320 (48844842382059 / 100000) (48851430614713 / 100000) := by
  exact
    packedTile32768 488470784 488536320 13 3293 22101 29 _ _ (1000339 / 50000) (2000681 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488536320 :
    ThetaLowerSegment 488536320 488601856 (48851430614713 / 100000) (48857924857699 / 100000) := by
  exact
    packedTile32768 488536320 488601856 13 3246 22102 29 _ _ (2000691 / 100000) (1000347 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488601856 :
    ThetaLowerSegment 488601856 488667392 (48857924857699 / 100000) (48864471161187 / 100000) := by
  exact
    packedTile32768 488601856 488667392 13 3272 22104 29 _ _ (62522 / 3125) (2000707 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488667392 :
    ThetaLowerSegment 488667392 488732928 (48864471161187 / 100000) (48871041519099 / 100000) := by
  exact
    packedTile32768 488667392 488732928 13 3284 22105 29 _ _ (1000359 / 50000) (2000721 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488732928 :
    ThetaLowerSegment 488732928 488798464 (48871041519099 / 100000) (305484411756 / 625) := by
  exact
    packedTile32768 488732928 488798464 13 3231 22107 29 _ _ (2000731 / 100000) (1000367 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488798464 :
    ThetaLowerSegment 488798464 488864000 (305484411756 / 625) (9776819667147 / 20000) := by
  exact
    packedTile32768 488798464 488864000 13 3295 22108 29 _ _ (400149 / 20000) (500187 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488864000 :
    ThetaLowerSegment 488864000 488929536 (9776819667147 / 20000) (9778120159847 / 20000) := by
  exact
    packedTile32768 488864000 488929536 13 3250 22110 29 _ _ (1000379 / 50000) (2000761 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488929536 :
    ThetaLowerSegment 488929536 488995072 (9778120159847 / 20000) (1528035291094 / 3125) := by
  exact
    packedTile32768 488929536 488995072 13 3263 22111 29 _ _ (2000771 / 100000) (1000387 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell488995072 :
    ThetaLowerSegment 488995072 489060608 (1528035291094 / 3125) (48903661878033 / 100000) := by
  exact
    packedTile32768 488995072 489060608 13 3265 22113 29 _ _ (400157 / 20000) (500197 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489060608 :
    ThetaLowerSegment 489060608 489126144 (48903661878033 / 100000) (48910256508241 / 100000) := by
  exact
    packedTile32768 489060608 489126144 13 3296 22114 29 _ _ (1000399 / 50000) (2000801 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489126144 :
    ThetaLowerSegment 489126144 489191680 (48910256508241 / 100000) (48916817170789 / 100000) := by
  exact
    packedTile32768 489126144 489191680 13 3279 22116 29 _ _ (500203 / 25000) (400163 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489191680 :
    ThetaLowerSegment 489191680 489257216 (48916817170789 / 100000) (48923359868539 / 100000) := by
  exact
    packedTile32768 489191680 489257216 13 3270 22117 29 _ _ (80033 / 4000) (500207 / 25000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489257216 :
    ThetaLowerSegment 489257216 489322752 (48923359868539 / 100000) (48929992646509 / 100000) := by
  exact
    packedTile32768 489257216 489322752 13 3315 22119 29 _ _ (1000419 / 50000) (2000841 / 100000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489322752 :
    ThetaLowerSegment 489322752 489339136 (48929992646509 / 100000) (9786337873801 / 20000) := by
  exact
    packedTile32768 489322752 489339136 11 848 22120 29 _ _ (500213 / 25000) (400171 / 20000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

private theorem cell489339136 :
    ThetaLowerSegment 489339136 489341184 (9786337873801 / 20000) (9786377090559 / 20000) := by
  exact
    packedTile32768 489339136 489341184 8 98 22121 29 _ _ (400171 / 20000) (1000429 / 50000)
      (by decide) (by decide) (by decide) (by decide +kernel) (by decide) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)

/-- The verified prime counts propagate the entry bound across this closed interval. -/
theorem theta_segment_457341184_489341184 :
    ThetaLowerSegment 457341184 489341184 (45732012740827 / 100000) (9786377090559 / 20000) := by
  exact
    (ThetaLowerSegment.join
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell457341184 cell457406720)
                    (ThetaLowerSegment.join cell457472256 cell457537792))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell457603328 cell457668864)
                    (ThetaLowerSegment.join cell457734400 cell457799936)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell457865472 cell457931008)
                    (ThetaLowerSegment.join cell457996544 cell458062080))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell458127616 cell458193152)
                    (ThetaLowerSegment.join cell458258688 cell458324224))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell458389760 cell458455296)
                    (ThetaLowerSegment.join cell458520832 cell458586368))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell458651904 cell458717440)
                    (ThetaLowerSegment.join cell458782976 cell458848512)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell458914048 cell458979584)
                    (ThetaLowerSegment.join cell459045120 cell459110656))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell459176192 cell459241728)
                    (ThetaLowerSegment.join cell459307264 cell459372800)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell459438336 cell459503872)
                    (ThetaLowerSegment.join cell459569408 cell459634944))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell459700480 cell459766016)
                    (ThetaLowerSegment.join cell459831552 cell459897088)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell459962624 cell460028160)
                    (ThetaLowerSegment.join cell460093696 cell460159232))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell460224768 cell460290304)
                    (ThetaLowerSegment.join cell460355840 cell460421376))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell460486912 cell460552448)
                    (ThetaLowerSegment.join cell460617984 cell460683520))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell460749056 cell460814592)
                    (ThetaLowerSegment.join cell460880128 cell460945664)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell461011200 cell461076736)
                    (ThetaLowerSegment.join cell461142272 cell461207808))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell461273344 cell461338880)
                    (ThetaLowerSegment.join cell461404416 cell461469952))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell461535488 cell461601024)
                    (ThetaLowerSegment.join cell461666560 cell461732096))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell461797632 cell461863168)
                    (ThetaLowerSegment.join cell461928704 cell461994240)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell462059776 cell462125312)
                    (ThetaLowerSegment.join cell462190848 cell462256384))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell462321920 cell462387456)
                    (ThetaLowerSegment.join cell462452992 cell462518528))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell462584064 cell462649600)
                    (ThetaLowerSegment.join cell462715136 cell462780672))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell462846208 cell462911744)
                    (ThetaLowerSegment.join cell462977280 cell463042816)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell463108352 cell463173888)
                    (ThetaLowerSegment.join cell463239424 cell463304960))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell463370496 cell463436032)
                    (ThetaLowerSegment.join cell463501568 cell463567104)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell463632640 cell463698176)
                    (ThetaLowerSegment.join cell463763712 cell463829248))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell463894784 cell463960320)
                    (ThetaLowerSegment.join cell464025856 cell464091392)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell464156928 cell464222464)
                    (ThetaLowerSegment.join cell464288000 cell464353536))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell464419072 cell464484608)
                    (ThetaLowerSegment.join cell464550144 cell464615680))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell464681216 cell464746752)
                    (ThetaLowerSegment.join cell464812288 cell464877824))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell464943360 cell465008896)
                    (ThetaLowerSegment.join cell465074432 cell465139968)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell465205504 cell465271040)
                    (ThetaLowerSegment.join cell465336576 cell465402112))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell465467648 cell465533184)
                    (ThetaLowerSegment.join cell465598720 cell465664256)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell465729792 cell465795328)
                    (ThetaLowerSegment.join cell465860864 cell465926400))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell465991936 cell466057472)
                    (ThetaLowerSegment.join cell466123008 cell466188544)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell466254080 cell466319616)
                    (ThetaLowerSegment.join cell466385152 cell466450688))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell466516224 cell466581760)
                    (ThetaLowerSegment.join cell466647296 cell466712832))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell466778368 cell466843904)
                    (ThetaLowerSegment.join cell466909440 cell466974976))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell467040512 cell467106048)
                    (ThetaLowerSegment.join cell467171584 cell467237120)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell467302656 cell467368192)
                    (ThetaLowerSegment.join cell467433728 cell467499264))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell467564800 cell467630336)
                    (ThetaLowerSegment.join cell467695872 cell467761408)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell467826944 cell467892480)
                    (ThetaLowerSegment.join cell467958016 cell468023552))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell468089088 cell468154624)
                    (ThetaLowerSegment.join cell468220160 cell468285696)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell468351232 cell468416768)
                    (ThetaLowerSegment.join cell468482304 cell468547840))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell468613376 cell468678912)
                    (ThetaLowerSegment.join cell468744448 cell468809984))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell468875520 cell468941056)
                    (ThetaLowerSegment.join cell469006592 cell469072128))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell469137664 cell469203200)
                    (ThetaLowerSegment.join cell469268736 cell469334272)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell469399808 cell469465344)
                    (ThetaLowerSegment.join cell469530880 cell469596416))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell469661952 cell469727488)
                    (ThetaLowerSegment.join cell469793024 cell469858560))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell469924096 cell469989632)
                    (ThetaLowerSegment.join cell470055168 cell470120704))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell470186240 cell470251776)
                    (ThetaLowerSegment.join cell470317312 cell470382848)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell470448384 cell470513920)
                    (ThetaLowerSegment.join cell470579456 cell470644992))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell470710528 cell470776064)
                    (ThetaLowerSegment.join cell470841600 cell470907136))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell470972672 cell471038208)
                    (ThetaLowerSegment.join cell471103744 cell471169280))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell471234816 cell471300352)
                    (ThetaLowerSegment.join cell471365888 cell471431424)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell471496960 cell471562496)
                    (ThetaLowerSegment.join cell471628032 cell471693568))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell471759104 cell471824640)
                    (ThetaLowerSegment.join cell471890176 cell471955712)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell472021248 cell472086784)
                    (ThetaLowerSegment.join cell472152320 cell472217856))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell472283392 cell472348928)
                    (ThetaLowerSegment.join cell472414464 cell472480000)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell472545536 cell472611072)
                    (ThetaLowerSegment.join cell472676608 cell472742144))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell472807680 cell472873216)
                    (ThetaLowerSegment.join cell472938752 cell473004288))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell473069824 cell473135360)
                    (ThetaLowerSegment.join cell473200896 cell473266432))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell473331968 cell473397504)
                    (ThetaLowerSegment.join cell473463040 cell473528576)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell473594112 cell473659648)
                    (ThetaLowerSegment.join cell473725184 cell473790720))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell473856256 cell473921792)
                    (ThetaLowerSegment.join cell473987328 cell474052864))))))))
      (ThetaLowerSegment.join
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell474118400 cell474183936)
                    (ThetaLowerSegment.join cell474249472 cell474315008))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell474380544 cell474446080)
                    (ThetaLowerSegment.join cell474511616 cell474577152)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell474642688 cell474708224)
                    (ThetaLowerSegment.join cell474773760 cell474839296))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell474904832 cell474970368)
                    (ThetaLowerSegment.join cell475035904 cell475101440))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell475166976 cell475232512)
                    (ThetaLowerSegment.join cell475298048 cell475363584))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell475429120 cell475494656)
                    (ThetaLowerSegment.join cell475560192 cell475625728)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell475691264 cell475756800)
                    (ThetaLowerSegment.join cell475822336 cell475887872))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell475953408 cell476018944)
                    (ThetaLowerSegment.join cell476084480 cell476150016)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell476215552 cell476281088)
                    (ThetaLowerSegment.join cell476346624 cell476412160))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell476477696 cell476543232)
                    (ThetaLowerSegment.join cell476608768 cell476674304)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell476739840 cell476805376)
                    (ThetaLowerSegment.join cell476870912 cell476936448))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell477001984 cell477067520)
                    (ThetaLowerSegment.join cell477133056 cell477198592))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell477264128 cell477329664)
                    (ThetaLowerSegment.join cell477395200 cell477460736))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell477526272 cell477591808)
                    (ThetaLowerSegment.join cell477657344 cell477722880)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell477788416 cell477853952)
                    (ThetaLowerSegment.join cell477919488 cell477985024))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell478050560 cell478116096)
                    (ThetaLowerSegment.join cell478181632 cell478247168))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell478312704 cell478378240)
                    (ThetaLowerSegment.join cell478443776 cell478509312))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell478574848 cell478640384)
                    (ThetaLowerSegment.join cell478705920 cell478771456)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell478836992 cell478902528)
                    (ThetaLowerSegment.join cell478968064 cell479033600))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell479099136 cell479164672)
                    (ThetaLowerSegment.join cell479230208 cell479295744))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell479361280 cell479426816)
                    (ThetaLowerSegment.join cell479492352 cell479557888))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell479623424 cell479688960)
                    (ThetaLowerSegment.join cell479754496 cell479820032)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell479885568 cell479951104)
                    (ThetaLowerSegment.join cell480016640 cell480082176))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell480147712 cell480213248)
                    (ThetaLowerSegment.join cell480278784 cell480344320)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell480409856 cell480475392)
                    (ThetaLowerSegment.join cell480540928 cell480606464))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell480672000 cell480737536)
                    (ThetaLowerSegment.join cell480803072 cell480868608)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell480934144 cell480999680)
                    (ThetaLowerSegment.join cell481065216 cell481130752))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell481196288 cell481261824)
                    (ThetaLowerSegment.join cell481327360 cell481392896))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell481458432 cell481523968)
                    (ThetaLowerSegment.join cell481589504 cell481655040))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell481720576 cell481786112)
                    (ThetaLowerSegment.join cell481851648 cell481917184)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell481982720 cell482048256)
                    (ThetaLowerSegment.join cell482113792 cell482179328))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell482244864 cell482310400)
                    (ThetaLowerSegment.join cell482375936 cell482441472)))))))
        (ThetaLowerSegment.join
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell482507008 cell482572544)
                    (ThetaLowerSegment.join cell482638080 cell482703616))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell482769152 cell482834688)
                    (ThetaLowerSegment.join cell482900224 cell482965760)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell483031296 cell483096832)
                    (ThetaLowerSegment.join cell483162368 cell483227904))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell483293440 cell483358976)
                    (ThetaLowerSegment.join cell483424512 cell483490048))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell483555584 cell483621120)
                    (ThetaLowerSegment.join cell483686656 cell483752192))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell483817728 cell483883264)
                    (ThetaLowerSegment.join cell483948800 cell484014336)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell484079872 cell484145408)
                    (ThetaLowerSegment.join cell484210944 cell484276480))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell484342016 cell484407552)
                    (ThetaLowerSegment.join cell484473088 cell484538624)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell484604160 cell484669696)
                    (ThetaLowerSegment.join cell484735232 cell484800768))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell484866304 cell484931840)
                    (ThetaLowerSegment.join cell484997376 cell485062912)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell485128448 cell485193984)
                    (ThetaLowerSegment.join cell485259520 cell485325056))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell485390592 cell485456128)
                    (ThetaLowerSegment.join cell485521664 cell485587200))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell485652736 cell485718272)
                    (ThetaLowerSegment.join cell485783808 cell485849344))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell485914880 cell485980416)
                    (ThetaLowerSegment.join cell486045952 cell486111488)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell486177024 cell486242560)
                    (ThetaLowerSegment.join cell486308096 cell486373632))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell486439168 cell486504704)
                    (ThetaLowerSegment.join cell486570240 cell486635776))))))
          (ThetaLowerSegment.join
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell486701312 cell486766848)
                    (ThetaLowerSegment.join cell486832384 cell486897920))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell486963456 cell487028992)
                    (ThetaLowerSegment.join cell487094528 cell487160064)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell487225600 cell487291136)
                    (ThetaLowerSegment.join cell487356672 cell487422208))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell487487744 cell487553280)
                    (ThetaLowerSegment.join cell487618816 cell487684352))))
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell487749888 cell487815424)
                    (ThetaLowerSegment.join cell487880960 cell487946496))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell488012032 cell488077568)
                    (ThetaLowerSegment.join cell488143104 cell488208640)))
                (ThetaLowerSegment.join
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell488274176 cell488339712)
                    (ThetaLowerSegment.join cell488405248 cell488470784))
                  (ThetaLowerSegment.join (ThetaLowerSegment.join cell488536320 cell488601856)
                    (ThetaLowerSegment.join cell488667392 cell488732928)))))
            (ThetaLowerSegment.join
              (ThetaLowerSegment.join
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell488798464 cell488864000)
                  (ThetaLowerSegment.join cell488929536 cell488995072))
                (ThetaLowerSegment.join (ThetaLowerSegment.join cell489060608 cell489126144)
                  (ThetaLowerSegment.join cell489191680 cell489257216)))
              (ThetaLowerSegment.join cell489322752 cell489339136))))))

end PseudoPrime.AnalyticNumberTheory.Cert.Chebyshev.ThetaLeeNosal
