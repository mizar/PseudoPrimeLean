/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperCell5Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaChunkSum

/-! # Principal upper aggregation chunk probes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

theorem gammaUpperCell5Chunk0 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              0).take
          128).sum ≤
      ((74628132401 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk1 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              128).take
          128).sum ≤
      ((13925349461 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk2 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              256).take
          128).sum ≤
      ((13104901 / 62500000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk3 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              384).take
          128).sum ≤
      ((30511631 / 2500000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk4 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              512).take
          128).sum ≤
      ((3086149 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk5 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              640).take
          128).sum ≤
      ((180929 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk6 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              768).take
          128).sum ≤
      ((14157 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk7 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              896).take
          128).sum ≤
      ((569 / 2000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk8 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1024).take
          128).sum ≤
      ((179 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk9 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1152).take
          128).sum ≤
      ((29 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk10 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1280).take
          128).sum ≤
      ((11 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk11 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1408).take
          128).sum ≤
      ((3 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk12 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1536).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk13 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1664).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk14 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1792).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk15 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              1920).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk16 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              2048).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk17 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              2176).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5Chunk18 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
                  gammaUpperCell5Exp).drop
              2304).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell5ChunksAbstract (xs : List ℚ)
    (h0 : ((xs.drop 0).take 128).sum ≤ ((74628132401 / 5000000000) : ℚ))
    (h1 : ((xs.drop 128).take 128).sum ≤ ((13925349461 / 5000000000) : ℚ))
    (h2 : ((xs.drop 256).take 128).sum ≤ ((13104901 / 62500000) : ℚ))
    (h3 : ((xs.drop 384).take 128).sum ≤ ((30511631 / 2500000000) : ℚ))
    (h4 : ((xs.drop 512).take 128).sum ≤ ((3086149 / 5000000000) : ℚ))
    (h5 : ((xs.drop 640).take 128).sum ≤ ((180929 / 5000000000) : ℚ))
    (h6 : ((xs.drop 768).take 128).sum ≤ ((14157 / 5000000000) : ℚ))
    (h7 : ((xs.drop 896).take 128).sum ≤ ((569 / 2000000000) : ℚ))
    (h8 : ((xs.drop 1024).take 128).sum ≤ ((179 / 5000000000) : ℚ))
    (h9 : ((xs.drop 1152).take 128).sum ≤ ((29 / 5000000000) : ℚ))
    (h10 : ((xs.drop 1280).take 128).sum ≤ ((11 / 10000000000) : ℚ))
    (h11 : ((xs.drop 1408).take 128).sum ≤ ((3 / 10000000000) : ℚ))
    (h12 : ((xs.drop 1536).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h13 : ((xs.drop 1664).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h14 : ((xs.drop 1792).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h15 : ((xs.drop 1920).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h16 : ((xs.drop 2048).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h17 : ((xs.drop 2176).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h18 : ((xs.drop 2304).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (hend : (xs.drop 2432).sum = 0) : xs.sum ≤ ((17933237 / 1000000) : ℚ) := by
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

theorem gammaUpperCell5ChunksSum :
    (List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell5Radius) (centerRowsBelow 20000)
          gammaUpperCell5Exp).sum ≤
      ((17933237 / 1000000) : ℚ) := by
  apply
    gammaUpperCell5ChunksAbstract _ gammaUpperCell5Chunk0 gammaUpperCell5Chunk1
      gammaUpperCell5Chunk2 gammaUpperCell5Chunk3 gammaUpperCell5Chunk4 gammaUpperCell5Chunk5
      gammaUpperCell5Chunk6 gammaUpperCell5Chunk7 gammaUpperCell5Chunk8 gammaUpperCell5Chunk9
      gammaUpperCell5Chunk10 gammaUpperCell5Chunk11 gammaUpperCell5Chunk12 gammaUpperCell5Chunk13
      gammaUpperCell5Chunk14 gammaUpperCell5Chunk15 gammaUpperCell5Chunk16 gammaUpperCell5Chunk17
      gammaUpperCell5Chunk18
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
