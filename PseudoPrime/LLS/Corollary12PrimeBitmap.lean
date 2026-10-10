/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.LLS.Corollary12PrimeCatalog

/-! A packed bitmap of the unchanged shared prime catalogue.
Regenerate with generate_corollary12_bitmap.py. -/

@[expose] public section

namespace PseudoPrime.LLS.Corollary12PrimeBitmap

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock0 : ℕ :=
  0x8028228800800a28028208820a00a08800228a20208828828208a20a08a28a8

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock1 : ℕ :=
  0x208808808008a20208828028020220208820808228020800228800200a20a082

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock2 : ℕ :=
  0x220808820808020200808220028208a00800a20828208020a08200820000a00

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock3 : ℕ :=
  bitmapBlock1 ||| (bitmapBlock2 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock4 : ℕ :=
  bitmapBlock0 ||| (bitmapBlock3 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock5 : ℕ :=
  0x28220020808208800208220200808800008a20008a20008028a00a0020080022

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock6 : ℕ :=
  0xa00008020020a08220020208200808028000020820208228800020a00a008280

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock7 : ℕ :=
  0x808008008228a00800828808228800200800020208200000000828008a20a08

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock8 : ℕ :=
  bitmapBlock6 ||| (bitmapBlock7 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock9 : ℕ :=
  bitmapBlock5 ||| (bitmapBlock8 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock10 : ℕ :=
  bitmapBlock4 ||| (bitmapBlock9 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock11 : ℕ :=
  0x28820000820820200a00200a2000002882000020082822822000880880822080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock12 : ℕ :=
  0x8028020808a20808200000a00028000208200200a288200080008080080200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock13 : ℕ :=
  0x220820228000808a00020208800000800020200a20a00028008028a00208020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock14 : ℕ :=
  bitmapBlock12 ||| (bitmapBlock13 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock15 : ℕ :=
  bitmapBlock11 ||| (bitmapBlock14 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock16 : ℕ :=
  0x20a08808020000800000220808008220008208008220a20800208828200000a0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock17 : ℕ :=
  0xa20a00200800220200a00828808228820808a008002002202000280080000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock18 : ℕ :=
  0x820020220008808028000000a08220008008020208200808000220808220008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock19 : ℕ :=
  bitmapBlock17 ||| (bitmapBlock18 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock20 : ℕ :=
  bitmapBlock16 ||| (bitmapBlock19 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock21 : ℕ :=
  bitmapBlock15 ||| (bitmapBlock20 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock22 : ℕ :=
  bitmapBlock10 ||| (bitmapBlock21 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock23 : ℕ :=
  0x8820828000000800a2800002022020800882002880000020002802000020880

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock24 : ℕ :=
  0xa00800a00828228020800808000028a20200020000208000a00028028008800a

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock25 : ℕ :=
  0x200a00008220008028200000820808020220800228008000820808220800200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock26 : ℕ :=
  bitmapBlock24 ||| (bitmapBlock25 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock27 : ℕ :=
  bitmapBlock23 ||| (bitmapBlock26 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock28 : ℕ :=
  0x28008200020a00000828208a00200000800008800a08a0880002022000802880

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock29 : ℕ :=
  0x200a00800000020208028028200a00a00a08020000020000a200082280008008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock30 : ℕ :=
  0x820808000820028000008a20800200a00008208820000a00200208000200820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock31 : ℕ :=
  bitmapBlock29 ||| (bitmapBlock30 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock32 : ℕ :=
  bitmapBlock28 ||| (bitmapBlock31 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock33 : ℕ :=
  bitmapBlock27 ||| (bitmapBlock32 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock34 : ℕ :=
  0x20000000800220028228800000808000220a00008008008200820a08a0002000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock35 : ℕ :=
  0x820828008220000808008000a00a088208002280208082280080208002002080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock36 : ℕ :=
  0x8800200800208200028200200000228800020020200808800208000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock37 : ℕ :=
  bitmapBlock35 ||| (bitmapBlock36 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock38 : ℕ :=
  bitmapBlock34 ||| (bitmapBlock37 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock39 : ℕ :=
  0x800000008020220820000008828008a00008a08000020a20800a2080820820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock40 : ℕ :=
  0x28028220a08800820208200808800000020a20000208020220800200a288280

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock41 : ℕ :=
  bitmapBlock39 ||| (bitmapBlock40 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock42 : ℕ :=
  0x8028020200200a00820800208820200008800008200000020008008800008200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock43 : ℕ :=
  0x20200820828200820208208028008020a08200800020220808a0000020080080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock44 : ℕ :=
  bitmapBlock42 ||| (bitmapBlock43 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock45 : ℕ :=
  bitmapBlock41 ||| (bitmapBlock44 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock46 : ℕ :=
  bitmapBlock38 ||| (bitmapBlock45 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock47 : ℕ :=
  bitmapBlock33 ||| (bitmapBlock46 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock48 : ℕ :=
  bitmapBlock22 ||| (bitmapBlock47 <<< 3072)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock49 : ℕ :=
  0x200020000800808000220a08028800020200000008020220000a000008200000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock50 : ℕ :=
  0x8808000800a08200020228800008028028000a00000220008020a00a00820028

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock51 : ℕ :=
  0x80800002820020800000802002000880080820022080820882802800000020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock52 : ℕ :=
  bitmapBlock50 ||| (bitmapBlock51 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock53 : ℕ :=
  bitmapBlock49 ||| (bitmapBlock52 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock54 : ℕ :=
  0x20800020000020000a000280200280200080000002088202008288002080200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock55 : ℕ :=
  0x220000208800020008800a08220028028220208200808028220000a08000200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock56 : ℕ :=
  0x20808008200008a20800200200208200000220000000a2002000882000880882

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock57 : ℕ :=
  bitmapBlock55 ||| (bitmapBlock56 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock58 : ℕ :=
  bitmapBlock54 ||| (bitmapBlock57 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock59 : ℕ :=
  bitmapBlock53 ||| (bitmapBlock58 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock60 : ℕ :=
  0x800808820008000008208020228200200820008000020a00020000000800a002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock61 : ℕ :=
  0x8800a08800000028020208020000020020800228800220800008228028020000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock62 : ℕ :=
  0x8220220208000820028800200a00020200800008a0082020020000000082000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock63 : ℕ :=
  bitmapBlock61 ||| (bitmapBlock62 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock64 : ℕ :=
  bitmapBlock60 ||| (bitmapBlock63 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock65 : ℕ :=
  0x8020220800000020800008a00200a080280088000088000202082208008208

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock66 : ℕ :=
  0x208800820200220800220800020800800000808020a00200028828000000a08

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock67 : ℕ :=
  bitmapBlock65 ||| (bitmapBlock66 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock68 : ℕ :=
  0x8a00000a28028200820800208000020a20008808000200a2000020002800820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock69 : ℕ :=
  0x28000020200a00020020800a088200200080000000088082002008002080082

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock70 : ℕ :=
  bitmapBlock68 ||| (bitmapBlock69 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock71 : ℕ :=
  bitmapBlock67 ||| (bitmapBlock70 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock72 : ℕ :=
  bitmapBlock64 ||| (bitmapBlock71 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock73 : ℕ :=
  bitmapBlock59 ||| (bitmapBlock72 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock74 : ℕ :=
  0x20800020200a08000820008800800a08008220020808008820028000208820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock75 : ℕ :=
  0x8008000200220208808028200000808828008028200000a0000002800000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock76 : ℕ :=
  0x8020008a20000228000000808000020020008228020200a002000288082088

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock77 : ℕ :=
  bitmapBlock75 ||| (bitmapBlock76 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock78 : ℕ :=
  bitmapBlock74 ||| (bitmapBlock77 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock79 : ℕ :=
  0x8220800a00008800008820800808800208220200000808000000a00020028

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock80 : ℕ :=
  0x8020808200020200a00000020800a0800082820802080000000802020080002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock81 : ℕ :=
  0x220808800000200020000228028020000800a20000208800a00a008000080000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock82 : ℕ :=
  bitmapBlock80 ||| (bitmapBlock81 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock83 : ℕ :=
  bitmapBlock79 ||| (bitmapBlock82 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock84 : ℕ :=
  bitmapBlock78 ||| (bitmapBlock83 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock85 : ℕ :=
  0x8000820a08008800008820008008008200800200028000020220800800808200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock86 : ℕ :=
  0x800800a00028020220000200000200220000220808000000a0000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock87 : ℕ :=
  0x8800008200a00820028208800208200800008800000828820208200208a

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock88 : ℕ :=
  bitmapBlock86 ||| (bitmapBlock87 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock89 : ℕ :=
  bitmapBlock85 ||| (bitmapBlock88 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock90 : ℕ :=
  0x220208028028008000808200000000a20208000008228220000028000020a20

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock91 : ℕ :=
  0x28008020808208808200020800220020220200800a2000000880020800002002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock92 : ℕ :=
  bitmapBlock90 ||| (bitmapBlock91 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock93 : ℕ :=
  0x8080200008200088000202008202000080082082200008280200208202000208

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock94 : ℕ :=
  0x208220000028a00008820808200200008a08808220000000020020020a00200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock95 : ℕ :=
  bitmapBlock93 ||| (bitmapBlock94 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock96 : ℕ :=
  bitmapBlock92 ||| (bitmapBlock95 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock97 : ℕ :=
  bitmapBlock89 ||| (bitmapBlock96 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock98 : ℕ :=
  bitmapBlock84 ||| (bitmapBlock97 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock99 : ℕ :=
  bitmapBlock73 ||| (bitmapBlock98 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock100 : ℕ :=
  bitmapBlock48 ||| (bitmapBlock99 <<< 6400)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock101 : ℕ :=
  0x20020800000808020200200a0000000882080880880000820020882000000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock102 : ℕ :=
  0x800200020008020008008020208208020000220800a00020008000000a088002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock103 : ℕ :=
  0x808020200008a08000020a00a00228828020000200020808200020800200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock104 : ℕ :=
  bitmapBlock102 ||| (bitmapBlock103 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock105 : ℕ :=
  bitmapBlock101 ||| (bitmapBlock104 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock106 : ℕ :=
  0x800208000220000a00a00000008800000028020208a00008a20008000200a0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock107 : ℕ :=
  0x8a00008020020000000a08000020008020000220008220800000000800008a

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock108 : ℕ :=
  0x8000000a20a08220008000800200800020028020808808820028000200000820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock109 : ℕ :=
  bitmapBlock107 ||| (bitmapBlock108 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock110 : ℕ :=
  bitmapBlock106 ||| (bitmapBlock109 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock111 : ℕ :=
  bitmapBlock105 ||| (bitmapBlock110 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock112 : ℕ :=
  0x800882020002000880880820822080822000800080020022000822820000002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock113 : ℕ :=
  0x2008082200202000008002200000008002002088080208000002088080280008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock114 : ℕ :=
  0x8020000a00820808028020a08800020208020000820800200200200a08020008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock115 : ℕ :=
  bitmapBlock113 ||| (bitmapBlock114 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock116 : ℕ :=
  bitmapBlock112 ||| (bitmapBlock115 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock117 : ℕ :=
  0x820000a0020080802000800080022000020820080880080020020080822002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock118 : ℕ :=
  0x800000000820208208800208200200a28800000000008808820028a002008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock119 : ℕ :=
  bitmapBlock117 ||| (bitmapBlock118 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock120 : ℕ :=
  0x8000808208800228a20000020000008200800028008000020008820820028220

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock121 : ℕ :=
  0x20020a00200820008000200000020800220000a0820000022880000000002800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock122 : ℕ :=
  bitmapBlock120 ||| (bitmapBlock121 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock123 : ℕ :=
  bitmapBlock119 ||| (bitmapBlock122 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock124 : ℕ :=
  bitmapBlock116 ||| (bitmapBlock123 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock125 : ℕ :=
  bitmapBlock111 ||| (bitmapBlock124 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock126 : ℕ :=
  0x280080088000000208202080002008000002082200000288002082208000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock127 : ℕ :=
  0x208808000000800a08008000008000008800820020000008828000200220a00

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock128 : ℕ :=
  0x20008200808200020000020820228200800020828000800008208820000a0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock129 : ℕ :=
  bitmapBlock127 ||| (bitmapBlock128 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock130 : ℕ :=
  bitmapBlock126 ||| (bitmapBlock129 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock131 : ℕ :=
  0x20228820000808020208220000828000000020000808000028800a080008080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock132 : ℕ :=
  0xa00000008800200a00028220000800800008020020a08208800020800800a00

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock133 : ℕ :=
  0xa08008020000800800a00800008000a08000020028020200020800000a0020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock134 : ℕ :=
  bitmapBlock132 ||| (bitmapBlock133 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock135 : ℕ :=
  bitmapBlock131 ||| (bitmapBlock134 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock136 : ℕ :=
  bitmapBlock130 ||| (bitmapBlock135 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock137 : ℕ :=
  0x20000208028828000020200200028028a00000020000028220800a00008020a

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock138 : ℕ :=
  0x800200220000808800200200200028820028000200228000220820800808020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock139 : ℕ :=
  0x808020000020000200000208800000020028000a2000802002000022080882

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock140 : ℕ :=
  bitmapBlock138 ||| (bitmapBlock139 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock141 : ℕ :=
  bitmapBlock137 ||| (bitmapBlock140 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock142 : ℕ :=
  0xa280080000002008000080000000082208002000202080080082002008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock143 : ℕ :=
  0xa00008200028000200000000828220000800208000220200000820008008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock144 : ℕ :=
  bitmapBlock142 ||| (bitmapBlock143 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock145 : ℕ :=
  0x820228a2000800882820000000002000802020020002080802002080082880

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock146 : ℕ :=
  0x200a00820000200000000000020820008208008200a00800000820020820a082

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock147 : ℕ :=
  bitmapBlock145 ||| (bitmapBlock146 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock148 : ℕ :=
  bitmapBlock144 ||| (bitmapBlock147 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock149 : ℕ :=
  bitmapBlock141 ||| (bitmapBlock148 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock150 : ℕ :=
  bitmapBlock136 ||| (bitmapBlock149 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock151 : ℕ :=
  bitmapBlock125 ||| (bitmapBlock150 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock152 : ℕ :=
  0xa00200200808200000a00000820200a00000820020200020008828008008020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock153 : ℕ :=
  0x8000200008220020028800208220820020000808008800020a0080022800820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock154 : ℕ :=
  0xa00000000a00800008808220000200a208202088000002008000202002000280

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock155 : ℕ :=
  bitmapBlock153 ||| (bitmapBlock154 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock156 : ℕ :=
  bitmapBlock152 ||| (bitmapBlock155 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock157 : ℕ :=
  0x800a00800200200008000028008000800820000000800a08020020028000008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock158 : ℕ :=
  0xa00008800808020200008a0080820002020000000002800020002800822880

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock159 : ℕ :=
  0x800008200800028808020820208800020008200200000828000000808a280200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock160 : ℕ :=
  bitmapBlock158 ||| (bitmapBlock159 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock161 : ℕ :=
  bitmapBlock157 ||| (bitmapBlock160 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock162 : ℕ :=
  bitmapBlock156 ||| (bitmapBlock161 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock163 : ℕ :=
  0x8828820008000000020008008220808a00000008200008a20000000820200000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock164 : ℕ :=
  0x20800a00800200200008020020028000000228028028020208a00000020a2000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock165 : ℕ :=
  0x2008208002000200008202000080002002008088080280002200088008002080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock166 : ℕ :=
  bitmapBlock164 ||| (bitmapBlock165 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock167 : ℕ :=
  bitmapBlock163 ||| (bitmapBlock166 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock168 : ℕ :=
  0x8008008000200000000220000800a20800220800a00028008208800800a08800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock169 : ℕ :=
  0x8020000a00200020820200000200208020028000208000000008800808a2

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock170 : ℕ :=
  bitmapBlock168 ||| (bitmapBlock169 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock171 : ℕ :=
  0x820200008028008220200a08008020000808a00028200000000028800020a008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock172 : ℕ :=
  0x8028220808020000200a00008200020008200000208028200000000208800008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock173 : ℕ :=
  bitmapBlock171 ||| (bitmapBlock172 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock174 : ℕ :=
  bitmapBlock170 ||| (bitmapBlock173 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock175 : ℕ :=
  bitmapBlock167 ||| (bitmapBlock174 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock176 : ℕ :=
  bitmapBlock162 ||| (bitmapBlock175 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock177 : ℕ :=
  0x28008020000800000800020a20200020808000800800200008008200808a2002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock178 : ℕ :=
  0x200a08000020020000020008008000800200008000000a002000082082008002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock179 : ℕ :=
  0x200200020820208a00000800000028020a08000000228800208820020008a20

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock180 : ℕ :=
  bitmapBlock178 ||| (bitmapBlock179 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock181 : ℕ :=
  bitmapBlock177 ||| (bitmapBlock180 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock182 : ℕ :=
  0x20020800208800820200220800200000020020a0082080822002000002880820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock183 : ℕ :=
  0x2000000002000000088080208000082000280200008002200202288208082080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock184 : ℕ :=
  0x800008800208020200800020220000008800028208000800828008000020200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock185 : ℕ :=
  bitmapBlock183 ||| (bitmapBlock184 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock186 : ℕ :=
  bitmapBlock182 ||| (bitmapBlock185 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock187 : ℕ :=
  bitmapBlock181 ||| (bitmapBlock186 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock188 : ℕ :=
  0x20020082002000880020002000002002080820800800000080800800020000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock189 : ℕ :=
  0x800200020000228000200000200a08800200800008a008000200200008088200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock190 : ℕ :=
  0x8800020028a00000000020208820200800000020800a08020800008220800200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock191 : ℕ :=
  bitmapBlock189 ||| (bitmapBlock190 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock192 : ℕ :=
  bitmapBlock188 ||| (bitmapBlock191 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock193 : ℕ :=
  0x208a00020000220008000000000000a08220808000800a0000800020802020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock194 : ℕ :=
  0x28200000800028200000808800820200020008020008208020008820020020a

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock195 : ℕ :=
  bitmapBlock193 ||| (bitmapBlock194 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock196 : ℕ :=
  0x8808000800000020020020220008a00020020000808828008200800200020800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock197 : ℕ :=
  0x200808000220200220000008a00a0020080002080020820802020020000082

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock198 : ℕ :=
  bitmapBlock196 ||| (bitmapBlock197 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock199 : ℕ :=
  bitmapBlock195 ||| (bitmapBlock198 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock200 : ℕ :=
  bitmapBlock192 ||| (bitmapBlock199 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock201 : ℕ :=
  bitmapBlock187 ||| (bitmapBlock200 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock202 : ℕ :=
  bitmapBlock176 ||| (bitmapBlock201 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock203 : ℕ :=
  bitmapBlock151 ||| (bitmapBlock202 <<< 6656)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock204 : ℕ :=
  bitmapBlock100 ||| (bitmapBlock203 <<< 13056)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock205 : ℕ :=
  0x2080002002200008000002002202008000080200208082008082080008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock206 : ℕ :=
  0x8000a00200820020200200008200008000020a08228028208a00200000820208

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock207 : ℕ :=
  0x80002880080022082800080080020800020820000082880000820000802802

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock208 : ℕ :=
  bitmapBlock206 ||| (bitmapBlock207 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock209 : ℕ :=
  bitmapBlock205 ||| (bitmapBlock208 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock210 : ℕ :=
  0x820000020200000008000a208008200280000008002080080000000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock211 : ℕ :=
  0x8000800208000000a00000008028028000200000828000020200208800028020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock212 : ℕ :=
  0x20200800000008800000820208828008208800a08a00000000220a0002000020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock213 : ℕ :=
  bitmapBlock211 ||| (bitmapBlock212 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock214 : ℕ :=
  bitmapBlock210 ||| (bitmapBlock213 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock215 : ℕ :=
  bitmapBlock209 ||| (bitmapBlock214 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock216 : ℕ :=
  0x8000000800a00a00820020000800008808000220008000820208a00000a000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock217 : ℕ :=
  0xa08000800000000a00000008028020208a00000000000200808020000a00008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock218 : ℕ :=
  0x20a2020800882800882080082800802822000022000820002000800080822000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock219 : ℕ :=
  bitmapBlock217 ||| (bitmapBlock218 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock220 : ℕ :=
  bitmapBlock216 ||| (bitmapBlock219 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock221 : ℕ :=
  0x8200202000008088080008200002208002200008008280000208008082008000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock222 : ℕ :=
  0x820800208020a08000020000020008800000208a20200000008000200200020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock223 : ℕ :=
  0x2020800800802880000800080820800080820080002000080800802002820080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock224 : ℕ :=
  bitmapBlock222 ||| (bitmapBlock223 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock225 : ℕ :=
  bitmapBlock221 ||| (bitmapBlock224 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock226 : ℕ :=
  bitmapBlock220 ||| (bitmapBlock225 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock227 : ℕ :=
  bitmapBlock215 ||| (bitmapBlock226 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock228 : ℕ :=
  0xa080000202200008008008202280000002088000002000080200002008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock229 : ℕ :=
  0x800008220000000028208800800220008000800200000028200200008200000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock230 : ℕ :=
  0x200820020200000820008220020a0000800800800020002800002080000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock231 : ℕ :=
  bitmapBlock229 ||| (bitmapBlock230 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock232 : ℕ :=
  bitmapBlock228 ||| (bitmapBlock231 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock233 : ℕ :=
  0x200008800000800a00000800008200008820800000000a008200200008008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock234 : ℕ :=
  0x208820200208020000820800000000200020000a20008020000200228000028

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock235 : ℕ :=
  0x8000020220800008000200200a0082002802002020800002020082000000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock236 : ℕ :=
  bitmapBlock234 ||| (bitmapBlock235 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock237 : ℕ :=
  bitmapBlock233 ||| (bitmapBlock236 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock238 : ℕ :=
  bitmapBlock232 ||| (bitmapBlock237 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock239 : ℕ :=
  0x808800000220a20000828808000a000000080280208008008200082000000002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock240 : ℕ :=
  0x220000000000000000000228808000020000220828008000000208808228020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock241 : ℕ :=
  0x2002820000080080000882000800080000820000802080000020080020800002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock242 : ℕ :=
  bitmapBlock240 ||| (bitmapBlock241 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock243 : ℕ :=
  bitmapBlock239 ||| (bitmapBlock242 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock244 : ℕ :=
  0x8020200820000000000008000808020008028000000000008200000a000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock245 : ℕ :=
  0x800220000200800a08020008000a00000a00008020820208a00000028000200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock246 : ℕ :=
  bitmapBlock244 ||| (bitmapBlock245 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock247 : ℕ :=
  0x8820800800800000a00208020020000200208820000008a00208a0000000022

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock248 : ℕ :=
  0x20000000a20800208000000020800000200208000808020a000002280000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock249 : ℕ :=
  bitmapBlock247 ||| (bitmapBlock248 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock250 : ℕ :=
  bitmapBlock246 ||| (bitmapBlock249 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock251 : ℕ :=
  bitmapBlock243 ||| (bitmapBlock250 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock252 : ℕ :=
  bitmapBlock238 ||| (bitmapBlock251 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock253 : ℕ :=
  bitmapBlock227 ||| (bitmapBlock252 <<< 3072)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock254 : ℕ :=
  0x8020008208800a00000028000020a00000800020000008828000000a20008808

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock255 : ℕ :=
  0x800000800808000028000200a0000000820800080802800022002020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock256 : ℕ :=
  0x20200008020808000220000000800020800800200008228000a002080200200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock257 : ℕ :=
  bitmapBlock255 ||| (bitmapBlock256 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock258 : ℕ :=
  bitmapBlock254 ||| (bitmapBlock257 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock259 : ℕ :=
  0x228020a00800000200800000800000008220208220008028200208000800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock260 : ℕ :=
  0x20008000000000000820000220808008000220000800208000028000a0020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock261 : ℕ :=
  0x2000080208282000008002280000008008008008000008000000000000002200

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock262 : ℕ :=
  bitmapBlock260 ||| (bitmapBlock261 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock263 : ℕ :=
  bitmapBlock259 ||| (bitmapBlock262 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock264 : ℕ :=
  bitmapBlock258 ||| (bitmapBlock263 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock265 : ℕ :=
  0x820000828028008800a00000008020200008000020028200800000008000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock266 : ℕ :=
  0x800000200008200800020200008020808208000a00008000008800a0000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock267 : ℕ :=
  0x828000008800000000020000a00000800000000000000208000020a000008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock268 : ℕ :=
  bitmapBlock266 ||| (bitmapBlock267 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock269 : ℕ :=
  bitmapBlock265 ||| (bitmapBlock268 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock270 : ℕ :=
  0x820800008028008020800000820000200000008008220200200208808020800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock271 : ℕ :=
  0x22000000822882002800080000002000002000880082000000000802000800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock272 : ℕ :=
  bitmapBlock270 ||| (bitmapBlock271 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock273 : ℕ :=
  0xa08000020a20000008008200000a000000000000200000000000000200082280

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock274 : ℕ :=
  0x8020020000020000220808000000208008000200800800a00008000800000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock275 : ℕ :=
  bitmapBlock273 ||| (bitmapBlock274 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock276 : ℕ :=
  bitmapBlock272 ||| (bitmapBlock275 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock277 : ℕ :=
  bitmapBlock269 ||| (bitmapBlock276 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock278 : ℕ :=
  bitmapBlock264 ||| (bitmapBlock277 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock279 : ℕ :=
  0x20000080080000002000800802000002020000880000020000020800000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock280 : ℕ :=
  0x8080080008088000200208000002200082280208000000000000000080200002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock281 : ℕ :=
  0x200800000200000028028000200000800000200000008208000200020000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock282 : ℕ :=
  bitmapBlock280 ||| (bitmapBlock281 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock283 : ℕ :=
  bitmapBlock279 ||| (bitmapBlock282 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock284 : ℕ :=
  0x20080000022000000002000082000082000000880000080000000802080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock285 : ℕ :=
  0x20a200008000202280000002200000000000080000200002008008000080008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock286 : ℕ :=
  0x8000200808820028020200200800020800008000820000000000200000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock287 : ℕ :=
  bitmapBlock285 ||| (bitmapBlock286 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock288 : ℕ :=
  bitmapBlock284 ||| (bitmapBlock287 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock289 : ℕ :=
  bitmapBlock283 ||| (bitmapBlock288 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock290 : ℕ :=
  0x8000208000800028008000a0000000080000002000080800000080020802

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock291 : ℕ :=
  0x8200000000000000208080000000002208000000008000000000000202

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock292 : ℕ :=
  0x800000000208000008800820200000000808000000200200000800020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock293 : ℕ :=
  bitmapBlock291 ||| (bitmapBlock292 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock294 : ℕ :=
  bitmapBlock290 ||| (bitmapBlock293 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock295 : ℕ :=
  0x28008020000a0002000000822000000000000020000000002000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock296 : ℕ :=
  0x8000080008000080000000288080000208000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock297 : ℕ :=
  bitmapBlock295 ||| (bitmapBlock296 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock298 : ℕ :=
  0x800000000000200020200000000000200000800000200000000000000200000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock299 : ℕ :=
  0x800000000000880800020000802002020000000000802022800020000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock300 : ℕ :=
  bitmapBlock298 ||| (bitmapBlock299 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock301 : ℕ :=
  bitmapBlock297 ||| (bitmapBlock300 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock302 : ℕ :=
  bitmapBlock294 ||| (bitmapBlock301 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock303 : ℕ :=
  bitmapBlock289 ||| (bitmapBlock302 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock304 : ℕ :=
  bitmapBlock278 ||| (bitmapBlock303 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock305 : ℕ :=
  bitmapBlock253 ||| (bitmapBlock304 <<< 6400)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock306 : ℕ :=
  0x8080080000008000008000000000000000000000008088000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock307 : ℕ :=
  0x20008020008000808000200000808008000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock308 : ℕ :=
  0x20020208028000008000000800000000000000a0000022000020000800000002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock309 : ℕ :=
  bitmapBlock307 ||| (bitmapBlock308 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock310 : ℕ :=
  bitmapBlock306 ||| (bitmapBlock309 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock311 : ℕ :=
  0x200000000000000002000080000000000000002000000000208000200002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock312 : ℕ :=
  0x200000000000000200800000000008000008000000000000808008000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock313 : ℕ :=
  0x20000000000002000000000022020000002000000800080000800000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock314 : ℕ :=
  bitmapBlock312 ||| (bitmapBlock313 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock315 : ℕ :=
  bitmapBlock311 ||| (bitmapBlock314 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock316 : ℕ :=
  bitmapBlock310 ||| (bitmapBlock315 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock317 : ℕ :=
  0xa000002000200208008002000000002000002000080008000000200000002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock318 : ℕ :=
  0x200000000000000000200000008000000000000800000000020000020800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock319 : ℕ :=
  0x8000200800000000020a0802000000000000080000800800000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock320 : ℕ :=
  bitmapBlock318 ||| (bitmapBlock319 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock321 : ℕ :=
  bitmapBlock317 ||| (bitmapBlock320 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock322 : ℕ :=
  0x8002000008200080000002008000008008080000002002000000080080000002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock323 : ℕ :=
  0x800000200000020000000800000000000008000020000800000820000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock324 : ℕ :=
  bitmapBlock322 ||| (bitmapBlock323 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock325 : ℕ :=
  0x800000800008200000000020800800008000000000000000000a0000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock326 : ℕ :=
  0x8000000000200002000000000008000000000000200008000000002000002000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock327 : ℕ :=
  bitmapBlock325 ||| (bitmapBlock326 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock328 : ℕ :=
  bitmapBlock324 ||| (bitmapBlock327 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock329 : ℕ :=
  bitmapBlock321 ||| (bitmapBlock328 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock330 : ℕ :=
  bitmapBlock316 ||| (bitmapBlock329 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock331 : ℕ :=
  0x200000820200020000000028000000008800008020000000000800008000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock332 : ℕ :=
  0x2000000000002000000080800020002000800000000880000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock333 : ℕ :=
  0x2000000000000000000000000008080000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock334 : ℕ :=
  bitmapBlock332 ||| (bitmapBlock333 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock335 : ℕ :=
  bitmapBlock331 ||| (bitmapBlock334 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock336 : ℕ :=
  0x800000000200800000000000200000000800000000000220000000a00000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock337 : ℕ :=
  0x20000000800200000800000000200000a0000080020000000000002000820

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock338 : ℕ :=
  0x20028000200000000000000000008000000000a000000200280008008000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock339 : ℕ :=
  bitmapBlock337 ||| (bitmapBlock338 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock340 : ℕ :=
  bitmapBlock336 ||| (bitmapBlock339 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock341 : ℕ :=
  bitmapBlock335 ||| (bitmapBlock340 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock342 : ℕ :=
  0x8000000000200800000000020000000200000020200000008000000000000020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock343 : ℕ :=
  0x2020002000020000020000002000080000000882020082000000000000000020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock344 : ℕ :=
  0x2000000000200000008000008200080000000000208080080000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock345 : ℕ :=
  bitmapBlock343 ||| (bitmapBlock344 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock346 : ℕ :=
  bitmapBlock342 ||| (bitmapBlock345 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock347 : ℕ :=
  0x800000200000000000000000000008000000000000800828000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock348 : ℕ :=
  0x20000000800800000000000080000000000000000000000002000080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock349 : ℕ :=
  bitmapBlock347 ||| (bitmapBlock348 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock350 : ℕ :=
  0x200000000000000000000000000000000000208000000000000200000080002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock351 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock352 : ℕ :=
  bitmapBlock350 ||| (bitmapBlock351 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock353 : ℕ :=
  bitmapBlock349 ||| (bitmapBlock352 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock354 : ℕ :=
  bitmapBlock346 ||| (bitmapBlock353 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock355 : ℕ :=
  bitmapBlock341 ||| (bitmapBlock354 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock356 : ℕ :=
  bitmapBlock330 ||| (bitmapBlock355 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock357 : ℕ :=
  0x800000002000000000020000000000020000000000000000000000800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock358 : ℕ :=
  0x80008080000200000080280000008000000000000008002

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock359 : ℕ :=
  0x8000000000000200000008000000008820000800008800008000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock360 : ℕ :=
  bitmapBlock358 ||| (bitmapBlock359 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock361 : ℕ :=
  bitmapBlock357 ||| (bitmapBlock360 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock362 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock363 : ℕ :=
  0x80000000200000000000000000000000000080002000000000000000088080

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock364 : ℕ :=
  0x8020000000008000000000000000000000000000000000800000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock365 : ℕ :=
  bitmapBlock363 ||| (bitmapBlock364 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock366 : ℕ :=
  bitmapBlock362 ||| (bitmapBlock365 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock367 : ℕ :=
  bitmapBlock361 ||| (bitmapBlock366 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock368 : ℕ :=
  0x2000000000000002000020000000000000020002000020000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock369 : ℕ :=
  0x8008200000000002002000000002002000000000000200000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock370 : ℕ :=
  0x8000000000000800000000000000000000000000008

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock371 : ℕ :=
  bitmapBlock369 ||| (bitmapBlock370 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock372 : ℕ :=
  bitmapBlock368 ||| (bitmapBlock371 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock373 : ℕ :=
  0x2000000000002000080000000000000000000020000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock374 : ℕ :=
  0x200000000000000000000000008000002000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock375 : ℕ :=
  bitmapBlock373 ||| (bitmapBlock374 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock376 : ℕ :=
  0x8000008020800000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock377 : ℕ :=
  0x800000002000000000000000000000000000002080020

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock378 : ℕ :=
  bitmapBlock376 ||| (bitmapBlock377 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock379 : ℕ :=
  bitmapBlock375 ||| (bitmapBlock378 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock380 : ℕ :=
  bitmapBlock372 ||| (bitmapBlock379 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock381 : ℕ :=
  bitmapBlock367 ||| (bitmapBlock380 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock382 : ℕ :=
  0x8000000000000008200000000080080000000000000000000000000002000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock383 : ℕ :=
  0x200000800000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock384 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock385 : ℕ :=
  bitmapBlock383 ||| (bitmapBlock384 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock386 : ℕ :=
  bitmapBlock382 ||| (bitmapBlock385 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock387 : ℕ :=
  0x200002000000000000008000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock388 : ℕ :=
  0x800000000008000000000000000000800000800000020000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock389 : ℕ :=
  0x80000002800000000000000000000000000002000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock390 : ℕ :=
  bitmapBlock388 ||| (bitmapBlock389 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock391 : ℕ :=
  bitmapBlock387 ||| (bitmapBlock390 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock392 : ℕ :=
  bitmapBlock386 ||| (bitmapBlock391 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock393 : ℕ :=
  0x8000000000000000200000000000000000080000008000000000000008000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock394 : ℕ :=
  0x800000000000000000000000200000000800000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock395 : ℕ :=
  0x2080000020000000000000000000000080000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock396 : ℕ :=
  bitmapBlock394 ||| (bitmapBlock395 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock397 : ℕ :=
  bitmapBlock393 ||| (bitmapBlock396 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock398 : ℕ :=
  0x200000000000000000000000000080000000002000000000000000000082

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock399 : ℕ :=
  0x800000000000000000000000000000020000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock400 : ℕ :=
  bitmapBlock398 ||| (bitmapBlock399 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock401 : ℕ :=
  0x8000000a0000000000000000000000000000002000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock402 : ℕ :=
  0x2080000002080000000000000008000000000000000002002000000000200000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock403 : ℕ :=
  bitmapBlock401 ||| (bitmapBlock402 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock404 : ℕ :=
  bitmapBlock400 ||| (bitmapBlock403 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock405 : ℕ :=
  bitmapBlock397 ||| (bitmapBlock404 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock406 : ℕ :=
  bitmapBlock392 ||| (bitmapBlock405 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock407 : ℕ :=
  bitmapBlock381 ||| (bitmapBlock406 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock408 : ℕ :=
  bitmapBlock356 ||| (bitmapBlock407 <<< 6656)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock409 : ℕ :=
  bitmapBlock305 ||| (bitmapBlock408 <<< 13056)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock410 : ℕ :=
  bitmapBlock204 ||| (bitmapBlock409 <<< 26368)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock411 : ℕ :=
  0x20000000000000200000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock412 : ℕ :=
  0x2000000002000000000020000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock413 : ℕ :=
  0x8000000000002000000000000000000200000000000000000000000000200000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock414 : ℕ :=
  bitmapBlock412 ||| (bitmapBlock413 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock415 : ℕ :=
  bitmapBlock411 ||| (bitmapBlock414 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock416 : ℕ :=
  0x800000000000000000000000000000000000000000000200000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock417 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock418 : ℕ :=
  0x2000080000000000000000000000000000000000000000000000080000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock419 : ℕ :=
  bitmapBlock417 ||| (bitmapBlock418 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock420 : ℕ :=
  bitmapBlock416 ||| (bitmapBlock419 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock421 : ℕ :=
  bitmapBlock415 ||| (bitmapBlock420 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock422 : ℕ :=
  0x8000000000800000000000000000008000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock423 : ℕ :=
  0x2000000000000800000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock424 : ℕ :=
  0x20200000020000000000000a000000000002000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock425 : ℕ :=
  bitmapBlock423 ||| (bitmapBlock424 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock426 : ℕ :=
  bitmapBlock422 ||| (bitmapBlock425 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock427 : ℕ :=
  0x8000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock428 : ℕ :=
  0x800000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock429 : ℕ :=
  0x200000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock430 : ℕ :=
  bitmapBlock428 ||| (bitmapBlock429 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock431 : ℕ :=
  bitmapBlock427 ||| (bitmapBlock430 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock432 : ℕ :=
  bitmapBlock426 ||| (bitmapBlock431 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock433 : ℕ :=
  bitmapBlock421 ||| (bitmapBlock432 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock434 : ℕ :=
  0x8000000000000000000000000000000000020000008000000000008800

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock435 : ℕ :=
  0x80000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock436 : ℕ :=
  0x8000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock437 : ℕ :=
  bitmapBlock435 ||| (bitmapBlock436 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock438 : ℕ :=
  bitmapBlock434 ||| (bitmapBlock437 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock439 : ℕ :=
  0x20000008200000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock440 : ℕ :=
  0x20000000000800000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock441 : ℕ :=
  0x2000000000008000000080080000000080000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock442 : ℕ :=
  bitmapBlock440 ||| (bitmapBlock441 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock443 : ℕ :=
  bitmapBlock439 ||| (bitmapBlock442 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock444 : ℕ :=
  bitmapBlock438 ||| (bitmapBlock443 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock445 : ℕ :=
  0x200000000000000000000000000000008000000000000200000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock446 : ℕ :=
  0x80800000000000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock447 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock448 : ℕ :=
  bitmapBlock446 ||| (bitmapBlock447 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock449 : ℕ :=
  bitmapBlock445 ||| (bitmapBlock448 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock450 : ℕ :=
  0x800000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock451 : ℕ :=
  0x80000000000000000000000000000000000800000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock452 : ℕ :=
  bitmapBlock450 ||| (bitmapBlock451 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock453 : ℕ :=
  0x80000000080000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock454 : ℕ :=
  0x800000000800200000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock455 : ℕ :=
  bitmapBlock453 ||| (bitmapBlock454 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock456 : ℕ :=
  bitmapBlock452 ||| (bitmapBlock455 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock457 : ℕ :=
  bitmapBlock449 ||| (bitmapBlock456 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock458 : ℕ :=
  bitmapBlock444 ||| (bitmapBlock457 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock459 : ℕ :=
  bitmapBlock433 ||| (bitmapBlock458 <<< 3072)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock460 : ℕ :=
  0x802000000000000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock461 : ℕ :=
  0x280000000000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock462 : ℕ :=
  0x808000000000000000020000000000000000800000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock463 : ℕ :=
  bitmapBlock461 ||| (bitmapBlock462 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock464 : ℕ :=
  bitmapBlock460 ||| (bitmapBlock463 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock465 : ℕ :=
  0x800000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock466 : ℕ :=
  0x80000000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock467 : ℕ :=
  0x808000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock468 : ℕ :=
  bitmapBlock466 ||| (bitmapBlock467 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock469 : ℕ :=
  bitmapBlock465 ||| (bitmapBlock468 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock470 : ℕ :=
  bitmapBlock464 ||| (bitmapBlock469 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock471 : ℕ :=
  0x80000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock472 : ℕ :=
  0x2000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock473 : ℕ :=
  0x20000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock474 : ℕ :=
  bitmapBlock472 ||| (bitmapBlock473 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock475 : ℕ :=
  bitmapBlock471 ||| (bitmapBlock474 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock476 : ℕ :=
  0x20000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock477 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock478 : ℕ :=
  bitmapBlock476 ||| (bitmapBlock477 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock479 : ℕ :=
  0x200000000000000000800000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock480 : ℕ :=
  0x800000020000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock481 : ℕ :=
  bitmapBlock479 ||| (bitmapBlock480 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock482 : ℕ :=
  bitmapBlock478 ||| (bitmapBlock481 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock483 : ℕ :=
  bitmapBlock475 ||| (bitmapBlock482 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock484 : ℕ :=
  bitmapBlock470 ||| (bitmapBlock483 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock485 : ℕ :=
  0x2000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock486 : ℕ :=
  0x8000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock487 : ℕ :=
  0x20000000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock488 : ℕ :=
  bitmapBlock486 ||| (bitmapBlock487 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock489 : ℕ :=
  bitmapBlock485 ||| (bitmapBlock488 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock490 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock491 : ℕ :=
  0x800000000000000000000000000000000000000020000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock492 : ℕ :=
  0x20000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock493 : ℕ :=
  bitmapBlock491 ||| (bitmapBlock492 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock494 : ℕ :=
  bitmapBlock490 ||| (bitmapBlock493 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock495 : ℕ :=
  bitmapBlock489 ||| (bitmapBlock494 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock496 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock497 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock498 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock499 : ℕ :=
  bitmapBlock497 ||| (bitmapBlock498 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock500 : ℕ :=
  bitmapBlock496 ||| (bitmapBlock499 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock501 : ℕ :=
  0x2000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock502 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock503 : ℕ :=
  bitmapBlock501 ||| (bitmapBlock502 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock504 : ℕ :=
  0x800000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock505 : ℕ :=
  0x80000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock506 : ℕ :=
  bitmapBlock504 ||| (bitmapBlock505 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock507 : ℕ :=
  bitmapBlock503 ||| (bitmapBlock506 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock508 : ℕ :=
  bitmapBlock500 ||| (bitmapBlock507 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock509 : ℕ :=
  bitmapBlock495 ||| (bitmapBlock508 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock510 : ℕ :=
  bitmapBlock484 ||| (bitmapBlock509 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock511 : ℕ :=
  bitmapBlock459 ||| (bitmapBlock510 <<< 6400)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock512 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock513 : ℕ :=
  0x800000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock514 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock515 : ℕ :=
  bitmapBlock513 ||| (bitmapBlock514 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock516 : ℕ :=
  bitmapBlock512 ||| (bitmapBlock515 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock517 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock518 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock519 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock520 : ℕ :=
  bitmapBlock518 ||| (bitmapBlock519 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock521 : ℕ :=
  bitmapBlock517 ||| (bitmapBlock520 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock522 : ℕ :=
  bitmapBlock516 ||| (bitmapBlock521 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock523 : ℕ :=
  0x8000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock524 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock525 : ℕ :=
  0x200000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock526 : ℕ :=
  bitmapBlock524 ||| (bitmapBlock525 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock527 : ℕ :=
  bitmapBlock523 ||| (bitmapBlock526 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock528 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock529 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock530 : ℕ :=
  bitmapBlock528 ||| (bitmapBlock529 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock531 : ℕ :=
  0x8000000000000000000000000000000000000002000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock532 : ℕ :=
  0x800000000200000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock533 : ℕ :=
  bitmapBlock531 ||| (bitmapBlock532 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock534 : ℕ :=
  bitmapBlock530 ||| (bitmapBlock533 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock535 : ℕ :=
  bitmapBlock527 ||| (bitmapBlock534 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock536 : ℕ :=
  bitmapBlock522 ||| (bitmapBlock535 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock537 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock538 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock539 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock540 : ℕ :=
  bitmapBlock538 ||| (bitmapBlock539 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock541 : ℕ :=
  bitmapBlock537 ||| (bitmapBlock540 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock542 : ℕ :=
  0x80000000000000000000000000000000000000000000020000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock543 : ℕ :=
  0x200000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock544 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock545 : ℕ :=
  bitmapBlock543 ||| (bitmapBlock544 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock546 : ℕ :=
  bitmapBlock542 ||| (bitmapBlock545 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock547 : ℕ :=
  bitmapBlock541 ||| (bitmapBlock546 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock548 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock549 : ℕ :=
  0x2000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock550 : ℕ :=
  0x800000000000020000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock551 : ℕ :=
  bitmapBlock549 ||| (bitmapBlock550 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock552 : ℕ :=
  bitmapBlock548 ||| (bitmapBlock551 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock553 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock554 : ℕ :=
  0x2000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock555 : ℕ :=
  bitmapBlock553 ||| (bitmapBlock554 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock556 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock557 : ℕ :=
  0x2000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock558 : ℕ :=
  bitmapBlock556 ||| (bitmapBlock557 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock559 : ℕ :=
  bitmapBlock555 ||| (bitmapBlock558 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock560 : ℕ :=
  bitmapBlock552 ||| (bitmapBlock559 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock561 : ℕ :=
  bitmapBlock547 ||| (bitmapBlock560 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock562 : ℕ :=
  bitmapBlock536 ||| (bitmapBlock561 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock563 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock564 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock565 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock566 : ℕ :=
  bitmapBlock564 ||| (bitmapBlock565 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock567 : ℕ :=
  bitmapBlock563 ||| (bitmapBlock566 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock568 : ℕ :=
  0x2000000000000000008000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock569 : ℕ :=
  0x200000000000000000000000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock570 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock571 : ℕ :=
  bitmapBlock569 ||| (bitmapBlock570 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock572 : ℕ :=
  bitmapBlock568 ||| (bitmapBlock571 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock573 : ℕ :=
  bitmapBlock567 ||| (bitmapBlock572 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock574 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock575 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock576 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock577 : ℕ :=
  bitmapBlock575 ||| (bitmapBlock576 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock578 : ℕ :=
  bitmapBlock574 ||| (bitmapBlock577 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock579 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock580 : ℕ :=
  0x200000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock581 : ℕ :=
  bitmapBlock579 ||| (bitmapBlock580 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock582 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock583 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock584 : ℕ :=
  bitmapBlock582 ||| (bitmapBlock583 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock585 : ℕ :=
  bitmapBlock581 ||| (bitmapBlock584 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock586 : ℕ :=
  bitmapBlock578 ||| (bitmapBlock585 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock587 : ℕ :=
  bitmapBlock573 ||| (bitmapBlock586 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock588 : ℕ :=
  0x20000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock589 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock590 : ℕ :=
  0x80000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock591 : ℕ :=
  bitmapBlock589 ||| (bitmapBlock590 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock592 : ℕ :=
  bitmapBlock588 ||| (bitmapBlock591 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock593 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock594 : ℕ :=
  0x80000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock595 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock596 : ℕ :=
  bitmapBlock594 ||| (bitmapBlock595 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock597 : ℕ :=
  bitmapBlock593 ||| (bitmapBlock596 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock598 : ℕ :=
  bitmapBlock592 ||| (bitmapBlock597 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock599 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock600 : ℕ :=
  0x80000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock601 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock602 : ℕ :=
  bitmapBlock600 ||| (bitmapBlock601 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock603 : ℕ :=
  bitmapBlock599 ||| (bitmapBlock602 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock604 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock605 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock606 : ℕ :=
  bitmapBlock604 ||| (bitmapBlock605 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock607 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock608 : ℕ :=
  0x20000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock609 : ℕ :=
  bitmapBlock607 ||| (bitmapBlock608 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock610 : ℕ :=
  bitmapBlock606 ||| (bitmapBlock609 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock611 : ℕ :=
  bitmapBlock603 ||| (bitmapBlock610 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock612 : ℕ :=
  bitmapBlock598 ||| (bitmapBlock611 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock613 : ℕ :=
  bitmapBlock587 ||| (bitmapBlock612 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock614 : ℕ :=
  bitmapBlock562 ||| (bitmapBlock613 <<< 6656)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock615 : ℕ :=
  bitmapBlock511 ||| (bitmapBlock614 <<< 13056)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock616 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock617 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock618 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock619 : ℕ :=
  bitmapBlock617 ||| (bitmapBlock618 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock620 : ℕ :=
  bitmapBlock616 ||| (bitmapBlock619 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock621 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock622 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock623 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock624 : ℕ :=
  bitmapBlock622 ||| (bitmapBlock623 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock625 : ℕ :=
  bitmapBlock621 ||| (bitmapBlock624 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock626 : ℕ :=
  bitmapBlock620 ||| (bitmapBlock625 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock627 : ℕ :=
  0x2000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock628 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock629 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock630 : ℕ :=
  bitmapBlock628 ||| (bitmapBlock629 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock631 : ℕ :=
  bitmapBlock627 ||| (bitmapBlock630 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock632 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock633 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock634 : ℕ :=
  bitmapBlock632 ||| (bitmapBlock633 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock635 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock636 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock637 : ℕ :=
  bitmapBlock635 ||| (bitmapBlock636 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock638 : ℕ :=
  bitmapBlock634 ||| (bitmapBlock637 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock639 : ℕ :=
  bitmapBlock631 ||| (bitmapBlock638 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock640 : ℕ :=
  bitmapBlock626 ||| (bitmapBlock639 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock641 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock642 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock643 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock644 : ℕ :=
  bitmapBlock642 ||| (bitmapBlock643 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock645 : ℕ :=
  bitmapBlock641 ||| (bitmapBlock644 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock646 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock647 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock648 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock649 : ℕ :=
  bitmapBlock647 ||| (bitmapBlock648 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock650 : ℕ :=
  bitmapBlock646 ||| (bitmapBlock649 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock651 : ℕ :=
  bitmapBlock645 ||| (bitmapBlock650 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock652 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock653 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock654 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock655 : ℕ :=
  bitmapBlock653 ||| (bitmapBlock654 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock656 : ℕ :=
  bitmapBlock652 ||| (bitmapBlock655 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock657 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock658 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock659 : ℕ :=
  bitmapBlock657 ||| (bitmapBlock658 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock660 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock661 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock662 : ℕ :=
  bitmapBlock660 ||| (bitmapBlock661 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock663 : ℕ :=
  bitmapBlock659 ||| (bitmapBlock662 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock664 : ℕ :=
  bitmapBlock656 ||| (bitmapBlock663 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock665 : ℕ :=
  bitmapBlock651 ||| (bitmapBlock664 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock666 : ℕ :=
  bitmapBlock640 ||| (bitmapBlock665 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock667 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock668 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock669 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock670 : ℕ :=
  bitmapBlock668 ||| (bitmapBlock669 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock671 : ℕ :=
  bitmapBlock667 ||| (bitmapBlock670 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock672 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock673 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock674 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock675 : ℕ :=
  bitmapBlock673 ||| (bitmapBlock674 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock676 : ℕ :=
  bitmapBlock672 ||| (bitmapBlock675 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock677 : ℕ :=
  bitmapBlock671 ||| (bitmapBlock676 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock678 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock679 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock680 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock681 : ℕ :=
  bitmapBlock679 ||| (bitmapBlock680 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock682 : ℕ :=
  bitmapBlock678 ||| (bitmapBlock681 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock683 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock684 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock685 : ℕ :=
  bitmapBlock683 ||| (bitmapBlock684 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock686 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock687 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock688 : ℕ :=
  bitmapBlock686 ||| (bitmapBlock687 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock689 : ℕ :=
  bitmapBlock685 ||| (bitmapBlock688 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock690 : ℕ :=
  bitmapBlock682 ||| (bitmapBlock689 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock691 : ℕ :=
  bitmapBlock677 ||| (bitmapBlock690 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock692 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock693 : ℕ :=
  0x80000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock694 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock695 : ℕ :=
  bitmapBlock693 ||| (bitmapBlock694 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock696 : ℕ :=
  bitmapBlock692 ||| (bitmapBlock695 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock697 : ℕ :=
  0x2000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock698 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock699 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock700 : ℕ :=
  bitmapBlock698 ||| (bitmapBlock699 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock701 : ℕ :=
  bitmapBlock697 ||| (bitmapBlock700 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock702 : ℕ :=
  bitmapBlock696 ||| (bitmapBlock701 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock703 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock704 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock705 : ℕ :=
  0x8000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock706 : ℕ :=
  bitmapBlock704 ||| (bitmapBlock705 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock707 : ℕ :=
  bitmapBlock703 ||| (bitmapBlock706 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock708 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock709 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock710 : ℕ :=
  bitmapBlock708 ||| (bitmapBlock709 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock711 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock712 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock713 : ℕ :=
  bitmapBlock711 ||| (bitmapBlock712 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock714 : ℕ :=
  bitmapBlock710 ||| (bitmapBlock713 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock715 : ℕ :=
  bitmapBlock707 ||| (bitmapBlock714 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock716 : ℕ :=
  bitmapBlock702 ||| (bitmapBlock715 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock717 : ℕ :=
  bitmapBlock691 ||| (bitmapBlock716 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock718 : ℕ :=
  bitmapBlock666 ||| (bitmapBlock717 <<< 6656)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock719 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock720 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock721 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock722 : ℕ :=
  bitmapBlock720 ||| (bitmapBlock721 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock723 : ℕ :=
  bitmapBlock719 ||| (bitmapBlock722 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock724 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock725 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock726 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock727 : ℕ :=
  bitmapBlock725 ||| (bitmapBlock726 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock728 : ℕ :=
  bitmapBlock724 ||| (bitmapBlock727 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock729 : ℕ :=
  bitmapBlock723 ||| (bitmapBlock728 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock730 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock731 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock732 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock733 : ℕ :=
  bitmapBlock731 ||| (bitmapBlock732 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock734 : ℕ :=
  bitmapBlock730 ||| (bitmapBlock733 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock735 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock736 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock737 : ℕ :=
  bitmapBlock735 ||| (bitmapBlock736 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock738 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock739 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock740 : ℕ :=
  bitmapBlock738 ||| (bitmapBlock739 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock741 : ℕ :=
  bitmapBlock737 ||| (bitmapBlock740 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock742 : ℕ :=
  bitmapBlock734 ||| (bitmapBlock741 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock743 : ℕ :=
  bitmapBlock729 ||| (bitmapBlock742 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock744 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock745 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock746 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock747 : ℕ :=
  bitmapBlock745 ||| (bitmapBlock746 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock748 : ℕ :=
  bitmapBlock744 ||| (bitmapBlock747 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock749 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock750 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock751 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock752 : ℕ :=
  bitmapBlock750 ||| (bitmapBlock751 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock753 : ℕ :=
  bitmapBlock749 ||| (bitmapBlock752 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock754 : ℕ :=
  bitmapBlock748 ||| (bitmapBlock753 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock755 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock756 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock757 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock758 : ℕ :=
  bitmapBlock756 ||| (bitmapBlock757 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock759 : ℕ :=
  bitmapBlock755 ||| (bitmapBlock758 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock760 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock761 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock762 : ℕ :=
  bitmapBlock760 ||| (bitmapBlock761 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock763 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock764 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock765 : ℕ :=
  bitmapBlock763 ||| (bitmapBlock764 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock766 : ℕ :=
  bitmapBlock762 ||| (bitmapBlock765 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock767 : ℕ :=
  bitmapBlock759 ||| (bitmapBlock766 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock768 : ℕ :=
  bitmapBlock754 ||| (bitmapBlock767 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock769 : ℕ :=
  bitmapBlock743 ||| (bitmapBlock768 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock770 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock771 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock772 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock773 : ℕ :=
  bitmapBlock771 ||| (bitmapBlock772 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock774 : ℕ :=
  bitmapBlock770 ||| (bitmapBlock773 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock775 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock776 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock777 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock778 : ℕ :=
  bitmapBlock776 ||| (bitmapBlock777 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock779 : ℕ :=
  bitmapBlock775 ||| (bitmapBlock778 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock780 : ℕ :=
  bitmapBlock774 ||| (bitmapBlock779 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock781 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock782 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock783 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock784 : ℕ :=
  bitmapBlock782 ||| (bitmapBlock783 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock785 : ℕ :=
  bitmapBlock781 ||| (bitmapBlock784 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock786 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock787 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock788 : ℕ :=
  bitmapBlock786 ||| (bitmapBlock787 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock789 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock790 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock791 : ℕ :=
  bitmapBlock789 ||| (bitmapBlock790 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock792 : ℕ :=
  bitmapBlock788 ||| (bitmapBlock791 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock793 : ℕ :=
  bitmapBlock785 ||| (bitmapBlock792 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock794 : ℕ :=
  bitmapBlock780 ||| (bitmapBlock793 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock795 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock796 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock797 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock798 : ℕ :=
  bitmapBlock796 ||| (bitmapBlock797 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock799 : ℕ :=
  bitmapBlock795 ||| (bitmapBlock798 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock800 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock801 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock802 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock803 : ℕ :=
  bitmapBlock801 ||| (bitmapBlock802 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock804 : ℕ :=
  bitmapBlock800 ||| (bitmapBlock803 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock805 : ℕ :=
  bitmapBlock799 ||| (bitmapBlock804 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock806 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock807 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock808 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock809 : ℕ :=
  bitmapBlock807 ||| (bitmapBlock808 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock810 : ℕ :=
  bitmapBlock806 ||| (bitmapBlock809 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock811 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock812 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock813 : ℕ :=
  bitmapBlock811 ||| (bitmapBlock812 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock814 : ℕ :=
  0x0

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock815 : ℕ :=
  0x200000000000000000000000000000000000000000000

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock816 : ℕ :=
  bitmapBlock814 ||| (bitmapBlock815 <<< 256)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock817 : ℕ :=
  bitmapBlock813 ||| (bitmapBlock816 <<< 512)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock818 : ℕ :=
  bitmapBlock810 ||| (bitmapBlock817 <<< 768)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock819 : ℕ :=
  bitmapBlock805 ||| (bitmapBlock818 <<< 1536)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock820 : ℕ :=
  bitmapBlock794 ||| (bitmapBlock819 <<< 3328)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock821 : ℕ :=
  bitmapBlock769 ||| (bitmapBlock820 <<< 6656)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock822 : ℕ :=
  bitmapBlock718 ||| (bitmapBlock821 <<< 13312)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock823 : ℕ :=
  bitmapBlock615 ||| (bitmapBlock822 <<< 26368)

/-- A balanced block of supplied catalogue bits. -/
def bitmapBlock824 : ℕ :=
  bitmapBlock410 ||| (bitmapBlock823 <<< 52736)

/-- Bit p records that p is one of the existing certified prime labels.
No completeness of the prime catalogue is asserted or required. -/
def primeBits : ℕ :=
  bitmapBlock824

/-- The packed bitmap equals the existing tree mask at its full cap.
Kernel evaluation checks the supplied encoding once, independently
of the primality proof shared by all finite coverage checks. -/
theorem primeBits_checked :
    NumberTheory.primeTreeResidueMask 105650 105649 Corollary12PrimeCatalog.catalog =
      primeBits := by
  decide +kernel

/-- Every set bitmap bit is a prime from the original certified tree.
Recover a tree witness and use the full cap to remove its modulus.
This supplies the shared primality premise of bitmap coverage. -/
theorem primeBits_prime {p : ℕ} (hp : primeBits.testBit p = true) : p.Prime := by
  obtain ⟨r, hr, hm, hcap⟩ :=
    NumberTheory.primeTreeResidueMask_exists Corollary12PrimeCatalog.catalog_checked
      (primeBits_checked.symm ▸ hp)
  have he : r = p := (Nat.mod_eq_of_lt (Nat.lt_succ_of_le hcap)).symm.trans hm
  exact he ▸ hr

end PseudoPrime.LLS.Corollary12PrimeBitmap
