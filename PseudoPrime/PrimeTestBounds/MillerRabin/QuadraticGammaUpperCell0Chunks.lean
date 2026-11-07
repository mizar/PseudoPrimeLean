/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperCell0Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaChunkSum

/-! # Principal upper aggregation chunk probes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

theorem upperChunk0 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              0).take
          128).sum ≤
      (74083342533 / 5000000000 : ℚ) := by
  decide +kernel

theorem upperChunk1 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              128).take
          128).sum ≤
      (25192781447 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk2 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              256).take
          128).sum ≤
      (1670691141 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk3 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              384).take
          128).sum ≤
      (42528769 / 5000000000 : ℚ) := by
  decide +kernel

theorem upperChunk4 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              512).take
          128).sum ≤
      (3825979 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk5 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              640).take
          128).sum ≤
      (13027 / 625000000 : ℚ) := by
  decide +kernel

theorem upperChunk6 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              768).take
          128).sum ≤
      (15647 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk7 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              896).take
          128).sum ≤
      (307 / 2000000000 : ℚ) := by
  decide +kernel

theorem upperChunk8 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1024).take
          128).sum ≤
      (19 / 1000000000 : ℚ) := by
  decide +kernel

theorem upperChunk9 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1152).take
          128).sum ≤
      (31 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk10 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1280).take
          128).sum ≤
      (3 / 5000000000 : ℚ) := by
  decide +kernel

theorem upperChunk11 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1408).take
          128).sum ≤
      (1 / 5000000000 : ℚ) := by
  decide +kernel

theorem upperChunk12 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1536).take
          128).sum ≤
      (1 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk13 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1664).take
          128).sum ≤
      (1 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk14 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1792).take
          128).sum ≤
      (1 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk15 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              1920).take
          128).sum ≤
      (1 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk16 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              2048).take
          128).sum ≤
      (1 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk17 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              2176).take
          128).sum ≤
      (1 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunk18 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
                  gammaUpperCell0Exp).drop
              2304).take
          128).sum ≤
      (1 / 10000000000 : ℚ) := by
  decide +kernel

theorem upperChunksAbstract (xs : List ℚ)
    (h0 : ((xs.drop 0).take 128).sum ≤ (74083342533 / 5000000000 : ℚ))
    (h1 : ((xs.drop 128).take 128).sum ≤ (25192781447 / 10000000000 : ℚ))
    (h2 : ((xs.drop 256).take 128).sum ≤ (1670691141 / 10000000000 : ℚ))
    (h3 : ((xs.drop 384).take 128).sum ≤ (42528769 / 5000000000 : ℚ))
    (h4 : ((xs.drop 512).take 128).sum ≤ (3825979 / 10000000000 : ℚ))
    (h5 : ((xs.drop 640).take 128).sum ≤ (13027 / 625000000 : ℚ))
    (h6 : ((xs.drop 768).take 128).sum ≤ (15647 / 10000000000 : ℚ))
    (h7 : ((xs.drop 896).take 128).sum ≤ (307 / 2000000000 : ℚ))
    (h8 : ((xs.drop 1024).take 128).sum ≤ (19 / 1000000000 : ℚ))
    (h9 : ((xs.drop 1152).take 128).sum ≤ (31 / 10000000000 : ℚ))
    (h10 : ((xs.drop 1280).take 128).sum ≤ (3 / 5000000000 : ℚ))
    (h11 : ((xs.drop 1408).take 128).sum ≤ (1 / 5000000000 : ℚ))
    (h12 : ((xs.drop 1536).take 128).sum ≤ (1 / 10000000000 : ℚ))
    (h13 : ((xs.drop 1664).take 128).sum ≤ (1 / 10000000000 : ℚ))
    (h14 : ((xs.drop 1792).take 128).sum ≤ (1 / 10000000000 : ℚ))
    (h15 : ((xs.drop 1920).take 128).sum ≤ (1 / 10000000000 : ℚ))
    (h16 : ((xs.drop 2048).take 128).sum ≤ (1 / 10000000000 : ℚ))
    (h17 : ((xs.drop 2176).take 128).sum ≤ (1 / 10000000000 : ℚ))
    (h18 : ((xs.drop 2304).take 128).sum ≤ (1 / 10000000000 : ℚ)) (hend : (xs.drop 2432).sum = 0) :
    xs.sum ≤ (17512 / 1000 : ℚ) := by
  have s0 := rational_list_chunk_sum xs 128
  have s1 := rational_list_chunk_sum (xs.drop 128) 128
  have s2 := rational_list_chunk_sum (xs.drop 256) 128
  have s3 := rational_list_chunk_sum (xs.drop 384) 128
  have s4 := rational_list_chunk_sum (xs.drop 512) 128
  have s5 := rational_list_chunk_sum (xs.drop 640) 128
  have s6 := rational_list_chunk_sum (xs.drop 768) 128
  have s7 := rational_list_chunk_sum (xs.drop 896) 128
  have s8 := rational_list_chunk_sum (xs.drop 1024) 128
  have s9 := rational_list_chunk_sum (xs.drop 1152) 128
  have s10 := rational_list_chunk_sum (xs.drop 1280) 128
  have s11 := rational_list_chunk_sum (xs.drop 1408) 128
  have s12 := rational_list_chunk_sum (xs.drop 1536) 128
  have s13 := rational_list_chunk_sum (xs.drop 1664) 128
  have s14 := rational_list_chunk_sum (xs.drop 1792) 128
  have s15 := rational_list_chunk_sum (xs.drop 1920) 128
  have s16 := rational_list_chunk_sum (xs.drop 2048) 128
  have s17 := rational_list_chunk_sum (xs.drop 2176) 128
  have s18 := rational_list_chunk_sum (xs.drop 2304) 128
  simp only [List.drop_drop, Nat.reduceAdd] at s1 s2 s3 s4 s5 s6 s7 s8 s9
  simp only [List.drop_drop, Nat.reduceAdd] at s10 s11 s12 s13 s14 s15 s16 s17 s18
  simp only [List.drop_zero] at h0
  linarith only [s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17,
    s18, h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18, hend]

theorem upperChunksSum :
    (List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell0Radius) (centerRowsBelow 20000)
          gammaUpperCell0Exp).sum ≤
      (17512 / 1000 : ℚ) := by
  apply
    upperChunksAbstract _ upperChunk0 upperChunk1 upperChunk2 upperChunk3 upperChunk4 upperChunk5
      upperChunk6 upperChunk7 upperChunk8 upperChunk9 upperChunk10 upperChunk11 upperChunk12
      upperChunk13 upperChunk14 upperChunk15 upperChunk16 upperChunk17 upperChunk18
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
