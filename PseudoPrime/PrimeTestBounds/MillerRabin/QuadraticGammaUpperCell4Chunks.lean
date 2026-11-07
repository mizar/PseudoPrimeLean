/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaUpperCell4Data
public import PseudoPrime.PrimeTestBounds.MillerRabin.QuadraticGammaChunkSum

/-! # Principal upper aggregation chunk probes -/

@[expose] public section

namespace PseudoPrime.PrimeTestBounds.MillerRabin

theorem gammaUpperCell4Chunk0 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              0).take
          128).sum ≤
      ((18638286121 / 1250000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk1 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              128).take
          128).sum ≤
      ((27456772189 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk2 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              256).take
          128).sum ≤
      ((1015083443 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk3 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              384).take
          128).sum ≤
      ((4637253 / 400000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk4 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              512).take
          128).sum ≤
      ((1152829 / 2000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk5 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              640).take
          128).sum ≤
      ((334267 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk6 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              768).take
          128).sum ≤
      ((25993 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk7 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              896).take
          128).sum ≤
      ((1301 / 5000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk8 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1024).take
          128).sum ≤
      ((327 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk9 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1152).take
          128).sum ≤
      ((53 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk10 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1280).take
          128).sum ≤
      ((1 / 1000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk11 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1408).take
          128).sum ≤
      ((3 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk12 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1536).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk13 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1664).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk14 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1792).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk15 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              1920).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk16 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              2048).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk17 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              2176).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4Chunk18 :
    (((List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
                  gammaUpperCell4Exp).drop
              2304).take
          128).sum ≤
      ((1 / 10000000000) : ℚ) := by
  decide +kernel

theorem gammaUpperCell4ChunksAbstract (xs : List ℚ)
    (h0 : ((xs.drop 0).take 128).sum ≤ ((18638286121 / 1250000000) : ℚ))
    (h1 : ((xs.drop 128).take 128).sum ≤ ((27456772189 / 10000000000) : ℚ))
    (h2 : ((xs.drop 256).take 128).sum ≤ ((1015083443 / 5000000000) : ℚ))
    (h3 : ((xs.drop 384).take 128).sum ≤ ((4637253 / 400000000) : ℚ))
    (h4 : ((xs.drop 512).take 128).sum ≤ ((1152829 / 2000000000) : ℚ))
    (h5 : ((xs.drop 640).take 128).sum ≤ ((334267 / 10000000000) : ℚ))
    (h6 : ((xs.drop 768).take 128).sum ≤ ((25993 / 10000000000) : ℚ))
    (h7 : ((xs.drop 896).take 128).sum ≤ ((1301 / 5000000000) : ℚ))
    (h8 : ((xs.drop 1024).take 128).sum ≤ ((327 / 10000000000) : ℚ))
    (h9 : ((xs.drop 1152).take 128).sum ≤ ((53 / 10000000000) : ℚ))
    (h10 : ((xs.drop 1280).take 128).sum ≤ ((1 / 1000000000) : ℚ))
    (h11 : ((xs.drop 1408).take 128).sum ≤ ((3 / 10000000000) : ℚ))
    (h12 : ((xs.drop 1536).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h13 : ((xs.drop 1664).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h14 : ((xs.drop 1792).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h15 : ((xs.drop 1920).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h16 : ((xs.drop 2048).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h17 : ((xs.drop 2176).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (h18 : ((xs.drop 2304).take 128).sum ≤ ((1 / 10000000000) : ℚ))
    (hend : (xs.drop 2432).sum = 0) : xs.sum ≤ ((17871529 / 1000000) : ℚ) := by
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

theorem gammaUpperCell4ChunksSum :
    (List.zipWith (fun r e ↦ r.hi * e / gammaUpperCell4Radius) (centerRowsBelow 20000)
          gammaUpperCell4Exp).sum ≤
      ((17871529 / 1000000) : ℚ) := by
  apply
    gammaUpperCell4ChunksAbstract _ gammaUpperCell4Chunk0 gammaUpperCell4Chunk1
      gammaUpperCell4Chunk2 gammaUpperCell4Chunk3 gammaUpperCell4Chunk4 gammaUpperCell4Chunk5
      gammaUpperCell4Chunk6 gammaUpperCell4Chunk7 gammaUpperCell4Chunk8 gammaUpperCell4Chunk9
      gammaUpperCell4Chunk10 gammaUpperCell4Chunk11 gammaUpperCell4Chunk12 gammaUpperCell4Chunk13
      gammaUpperCell4Chunk14 gammaUpperCell4Chunk15 gammaUpperCell4Chunk16 gammaUpperCell4Chunk17
      gammaUpperCell4Chunk18
  decide +kernel

end PseudoPrime.PrimeTestBounds.MillerRabin
