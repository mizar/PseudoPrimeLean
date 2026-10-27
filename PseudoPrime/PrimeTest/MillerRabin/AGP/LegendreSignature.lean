/-
Copyright (c) 2026 Mizar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mizar
-/

module

public import PseudoPrime.PrimeTest.MillerRabin.AGP.LocalLegendreCriterion
public import PseudoPrime.PrimeTest.MillerRabin.AGP.CarmichaelConstruction
public import PseudoPrime.PrimeTest.MillerRabin.AGP.UnitSubsetProduct
public import Mathlib.Combinatorics.Pigeonhole

/-! # Legendre sign classes for finite sets of bases

This file selects a large class of primes that have the same Legendre signs at
every base in a fixed finite set.
-/

@[expose] public section

namespace PseudoPrime.PrimeTest.MillerRabin.AGP

/--
Inputs: `P` is a finite set of primes, none of which divides any base in `W`.
The number of primes exceeds `N` times the number `2 ^ W.card` of sign vectors.

Claim: some subset `Q` contains more than `N` primes and every pair in `Q` has
the same Legendre symbol at every base in `W`.

Content: nonzero Legendre symbols at prime moduli are either `1` or `-1`, so
there are at most two choices per base and at most `2 ^ W.card` sign vectors.

Proof: encode each prime by its Boolean sign vector, apply the finite
pigeonhole principle, and use nonvanishing to recover equality of symbols.

Role: this is the sign-class selection step in the AGP construction. A separate
subset-product theorem must still provide the required Carmichael congruence.
-/
theorem exists_large_common_legendre_signature_class {P : Finset ℕ} (W : Finset ℕ) (N : ℕ)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hnotdiv : ∀ p ∈ P, ∀ b ∈ W, ¬p ∣ b)
    (hsize : 2 ^ W.card * N < P.card) :
    ∃ Q : Finset ℕ,
      Q ⊆ P ∧
        (∀ p ∈ Q, Nat.Prime p) ∧
        N < Q.card ∧
        ∀ p ∈ Q,
          ∀ q ∈ Q,
            ∀ b ∈ W,
              ∀ (hp : Nat.Prime p) (hq : Nat.Prime q),
                @legendreSym p ⟨hp⟩ (b : ℤ) = @legendreSym q ⟨hq⟩ (b : ℤ) := by
  classical
  let Base := { b // b ∈ W }
  let Color := Base → Bool
  have hColorCard : Fintype.card Color = 2 ^ W.card := by
    dsimp [Color, Base]
    rw [Fintype.card_fun, Fintype.card_coe]
    rfl
  let color : ℕ → Color := fun p b =>
    if hp : Nat.Prime p then if @legendreSym p ⟨hp⟩ (b.val : ℤ) = 1 then true else false else false
  have hsize' : Fintype.card Color * N < P.card := by
    rw [hColorCard]
    exact hsize
  have hmap : ∀ p ∈ P, color p ∈ (Finset.univ : Finset Color) := by
    intro p hp
    exact Finset.mem_univ _
  obtain ⟨c, _, hc⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (s := P) (t :=
      (Finset.univ : Finset Color)) (f := color) (n := N) hmap
      (by simpa only [Finset.card_univ] using hsize')
  let Q := P.filter fun p => color p = c
  refine ⟨Q, ?_, ?_, ?_, ?_⟩
  · intro p hp
    exact (Finset.mem_filter.mp hp).1
  · intro p hp
    exact hprime p ((Finset.mem_filter.mp hp).1)
  · simpa only [Q, Finset.card_filter] using hc
  · intro p hp q hq b hb hpPrime hqPrime
    have hpP : p ∈ P := (Finset.mem_filter.mp hp).1
    have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
    have hcP : color p = c := (Finset.mem_filter.mp hp).2
    have hcQ : color q = c := (Finset.mem_filter.mp hq).2
    have hcolor : color p = color q := hcP.trans hcQ.symm
    have hvalue : color p ⟨b, hb⟩ = color q ⟨b, hb⟩ := congrFun hcolor ⟨b, hb⟩
    have hpz : ((b : ℤ) : ZMod p) ≠ 0 := by
      intro hz
      have hZ : (p : ℤ) ∣ (b : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (b : ℤ) p).mp hz
      exact hnotdiv p hpP b hb (Int.natCast_dvd_natCast.mp hZ)
    have hqz : ((b : ℤ) : ZMod q) ≠ 0 := by
      intro hz
      have hZ : (q : ℤ) ∣ (b : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (b : ℤ) q).mp hz
      exact hnotdiv q hqP b hb (Int.natCast_dvd_natCast.mp hZ)
    rcases @legendreSym.eq_one_or_neg_one p ⟨hpPrime⟩ (b : ℤ) hpz with hpOne | hpNeg
    · have hcp : color p ⟨b, hb⟩ = true := by
        simp only [color, dite_eq_left hpPrime, ite_eq_left hpOne]
      have hcq : color q ⟨b, hb⟩ = true := hvalue.symm.trans hcp
      have hqOne : @legendreSym q ⟨hqPrime⟩ (b : ℤ) = 1 := by
        rcases @legendreSym.eq_one_or_neg_one q ⟨hqPrime⟩ (b : ℤ) hqz with h | h
        · exact h
        · have hqcode : color q ⟨b, hb⟩ = false := by
            have hqnot : @legendreSym q ⟨hqPrime⟩ (b : ℤ) ≠ 1 := by
              rw [h]
              norm_num only
            simp only [color, dite_eq_left hqPrime, ite_eq_right hqnot]
          rw [hqcode] at hcq
          cases hcq
      exact hpOne.trans hqOne.symm
    · have hpnot : @legendreSym p ⟨hpPrime⟩ (b : ℤ) ≠ 1 := by
        rw [hpNeg]
        norm_num only
      have hcp : color p ⟨b, hb⟩ = false := by
        simp only [color, dite_eq_left hpPrime, ite_eq_right hpnot]
      have hcq : color q ⟨b, hb⟩ = false := hvalue.symm.trans hcp
      have hqNeg : @legendreSym q ⟨hqPrime⟩ (b : ℤ) = -1 := by
        rcases @legendreSym.eq_one_or_neg_one q ⟨hqPrime⟩ (b : ℤ) hqz with h | h
        · have hqcode : color q ⟨b, hb⟩ = true := by
            simp only [color, dite_eq_left hqPrime, ite_eq_left h]
          rw [hqcode] at hcq
          cases hcq
        · exact h
      exact hpNeg.trans hqNeg.symm

/--
Inputs: a sufficiently large set of primes coprime to `L`, each of the form
`d * k + 1` with `d ∣ L`, where `k` is coprime to `L`.

Claim: an exceptional-prime-free subset has at least two elements, its product
is Carmichael, and its product is one modulo `L`.

Content: the erased Fourier subset product supplies the unit congruence, while
the progression conditions supply the congruence modulo `k` and the Korselt
divisibilities.

Proof: obtain the subset with at least two elements, restrict the prime and
progression conditions to it, and apply the finite-product theorem.

Role: this is the P2 Carmichael construction before the Legendre-signature
selection step.
-/
theorem exists_carmichael_subset_of_progression_primes (L : ℕ) [NeZero L] (hL : 2 < L)
    (hlambda : 3 ≤ ArithmeticFunction.carmichael L) [NeZero (ArithmeticFunction.carmichael L)]
    (P : Finset ℕ) (k : ℕ) (hkL : Nat.Coprime k L) (hprime : ∀ p ∈ P, Nat.Prime p)
    (hcoprime : ∀ p ∈ P, Nat.Coprime p L) (hprogression : ∀ p ∈ P, ∃ d, d ∣ L ∧ p = d * k + 1)
    (hlarge : (ArithmeticFunction.carmichael L : ℝ) * Real.log L < P.card) :
    ∃ U : Finset ℕ,
      U ⊆ P.erase (k * L + 1) ∧
        2 ≤ U.card ∧
        Nat.IsCarmichael (∏ p ∈ U, p) ∧
        (∀ p ∈ U, p - 1 ∣ k * L) ∧ k * L ∣ (∏ p ∈ U, p) - 1 ∧ (∏ p ∈ U, (p : ZMod L)) = 1 := by
  obtain ⟨U, hUP, hcard, _, hmodL⟩ :=
    exists_two_or_more_unit_product_eq_one_of_progression L hL hlambda P k hkL hcoprime hprogression
      hlarge
  have hprimeU : ∀ p ∈ U, Nat.Prime p := by
    intro p hp
    exact hprime p ((Finset.mem_erase.mp (hUP hp)).2)
  have hprogressionU : ∀ p ∈ U, ∃ d, d ∣ L ∧ p = d * k + 1 := by
    intro p hp
    exact hprogression p ((Finset.mem_erase.mp (hUP hp)).2)
  obtain ⟨hcar, horder, hproductMod⟩ :=
    isCarmichael_finset_prime_product_of_progression_unit_product L k hkL hprimeU hcard
      hprogressionU hmodL
  refine ⟨U, hUP, hcard, hcar, horder, hproductMod, hmodL⟩

/--
Inputs: `Q` is nonempty, no prime in `Q` divides a base in `W`, and each pair
of primes in `Q` has equal Legendre symbols at every such base.

Claim: for each base in `W`, all primes in `Q` have one common sign, either `1`
or `-1`.

Content: choose one prime in `Q` as the reference value; nonzero Legendre
symbols at prime moduli are signs.

Proof: use nondivisibility to rule out zero, apply the two-value Legendre
property, and transfer the reference value by pairwise equality.

Role: this converts the output of `exists_large_common_legendre_signature_class`
to the common-sign input of the P1 criterion.
-/
theorem common_legendre_sign_of_pairwise_signatures {Q : Finset ℕ} (W : Finset ℕ)
    (hprime : ∀ p ∈ Q, Nat.Prime p) (hnotdiv : ∀ p ∈ Q, ∀ b ∈ W, ¬p ∣ b)
    (hpair :
      ∀ p ∈ Q,
        ∀ q ∈ Q,
          ∀ b ∈ W,
            ∀ (hp : Nat.Prime p) (hq : Nat.Prime q),
              @legendreSym p ⟨hp⟩ (b : ℤ) = @legendreSym q ⟨hq⟩ (b : ℤ))
    (hQ : Q.Nonempty) :
    ∀ b ∈ W,
      ∃ σ : ℤ,
        (σ = 1 ∨ σ = -1) ∧ ∀ p ∈ Q, ∀ (hp : Nat.Prime p), @legendreSym p ⟨hp⟩ (b : ℤ) = σ := by
  intro b hb
  obtain ⟨p0, hp0⟩ := hQ
  have hp0Prime := hprime p0 hp0
  have hp0z : ((b : ℤ) : ZMod p0) ≠ 0 := by
    intro hz
    have hZ : (p0 : ℤ) ∣ (b : ℤ) := (ZMod.intCast_zmod_eq_zero_iff_dvd (b : ℤ) p0).mp hz
    exact hnotdiv p0 hp0 b hb (Int.natCast_dvd_natCast.mp hZ)
  rcases @legendreSym.eq_one_or_neg_one p0 ⟨hp0Prime⟩ (b : ℤ) hp0z with hOne | hNeg
  · refine ⟨1, Or.inl rfl, ?_⟩
    intro p hp hpp
    exact (hpair p hp p0 hp0 b hb hpp hp0Prime).trans hOne
  · refine ⟨-1, Or.inr rfl, ?_⟩
    intro p hp hpp
    exact (hpair p hp p0 hp0 b hb hpp hp0Prime).trans hNeg

/--
Inputs: a finite prime set `Q` whose members satisfy the common Korselt
divisibility condition, whose product is `1 mod K`, and whose Legendre
signatures agree at every base in `W`.

Claim: every base in `W` passes the strong Miller–Rabin test modulo the product
of `Q`.

Content: the common-sign lemma supplies P1's local condition, and the
Carmichael-product theorem supplies the modulus properties.

Proof: turn pairwise signature agreement into one sign per base, then apply the
finite-prime-product criterion.

Role: this assembles the sign-class and Carmichael-product parts of P2. The
finite-group subset-product theorem must still supply `Q` and its congruence.
-/
theorem strongMillerRabinPass_all_of_signature_class {Q : Finset ℕ} {K : ℕ} (W : Finset ℕ)
    (hprime : ∀ p ∈ Q, Nat.Prime p) (hcard : 2 ≤ Q.card) (horder : ∀ p ∈ Q, p - 1 ∣ K)
    (hproductMod : K ∣ (∏ p ∈ Q, p) - 1) (hpMod : ∀ p ∈ Q, p % 4 = 3) (hbase : ∀ b ∈ W, 0 < b)
    (hnotdiv : ∀ p ∈ Q, ∀ b ∈ W, ¬p ∣ b)
    (hpair :
      ∀ p ∈ Q,
        ∀ q ∈ Q,
          ∀ b ∈ W,
            ∀ (hp : Nat.Prime p) (hq : Nat.Prime q),
              @legendreSym p ⟨hp⟩ (b : ℤ) = @legendreSym q ⟨hq⟩ (b : ℤ)) :
    ∀ b ∈ W, PrimeTest.StrongMillerRabinPass (∏ p ∈ Q, p) (b : ZMod (∏ p ∈ Q, p)) := by
  have hQ : Q.Nonempty := Finset.card_pos.mp (lt_of_lt_of_le (by decide : 0 < 2) hcard)
  have hcommon := common_legendre_sign_of_pairwise_signatures W hprime hnotdiv hpair hQ
  exact
    strongMillerRabinPass_all_of_finset_prime_product W hprime hcard horder hproductMod hpMod hbase
      (fun b hb p hp => hnotdiv p hp b hb) hcommon

/--
Inputs: a sufficiently large finite prime set with the AGP progression,
coprimality, residue, and base-nondivisibility conditions.

Claim: a Carmichael product passes every strong Miller-Rabin test in `W`.

Content: partition the primes by their Legendre-sign vectors, then use the
exception-free subset product and Korselt conditions in one class.

Proof: choose a signature class larger than the floor of the subset-product
threshold, construct its Carmichael subset, and apply the P1 signature test.

Role: this assembles the finite combinatorial P2 construction from a supplied
prime set; producing such a set remains the P3 task.
-/
theorem exists_carmichael_strongMillerRabin_pass_all_of_large_progression_primes (L : ℕ) [NeZero L]
    (hL : 2 < L) (hlambda : 3 ≤ ArithmeticFunction.carmichael L)
    [NeZero (ArithmeticFunction.carmichael L)] (W P : Finset ℕ) (k : ℕ) (hkL : Nat.Coprime k L)
    (hprime : ∀ p ∈ P, Nat.Prime p) (hcoprime : ∀ p ∈ P, Nat.Coprime p L)
    (hprogression : ∀ p ∈ P, ∃ d, d ∣ L ∧ p = d * k + 1) (hpMod : ∀ p ∈ P, p % 4 = 3)
    (hbase : ∀ b ∈ W, 0 < b) (hnotdiv : ∀ p ∈ P, ∀ b ∈ W, ¬p ∣ b)
    (hsize : 2 ^ W.card * Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L) < P.card) :
    ∃ U : Finset ℕ,
      U ⊆ P ∧
        2 ≤ U.card ∧
        Nat.IsCarmichael (∏ p ∈ U, p) ∧
        ∀ b ∈ W, PrimeTest.StrongMillerRabinPass (∏ p ∈ U, p) (b : ZMod (∏ p ∈ U, p)) := by
  let N := Nat.floor ((ArithmeticFunction.carmichael L : ℝ) * Real.log L)
  obtain ⟨Q, hQP, hQprime, hQN, hQpair⟩ :=
    exists_large_common_legendre_signature_class W N hprime (fun p hp b hb => hnotdiv p hp b hb)
      hsize
  have hlargeQ : (ArithmeticFunction.carmichael L : ℝ) * Real.log L < Q.card := by
    apply (Nat.floor_lt (by positivity)).1
    simpa only [N] using hQN
  obtain ⟨U, hUQ, hUcard, hUcar, hUorder, hUproductMod, hUmodL⟩ :=
    exists_carmichael_subset_of_progression_primes L hL hlambda Q k hkL hQprime
      (fun p hp => hcoprime p (hQP hp)) (fun p hp => hprogression p (hQP hp)) hlargeQ
  have hprimeU : ∀ p ∈ U, Nat.Prime p := by
    intro p hp
    exact hQprime p ((Finset.mem_erase.mp (hUQ hp)).2)
  have hmod4U : ∀ p ∈ U, p % 4 = 3 := by
    intro p hp
    exact hpMod p (hQP ((Finset.mem_erase.mp (hUQ hp)).2))
  have hnotdivU : ∀ p ∈ U, ∀ b ∈ W, ¬p ∣ b := by
    intro p hp b hb
    exact hnotdiv p (hQP ((Finset.mem_erase.mp (hUQ hp)).2)) b hb
  have hpairU :
    ∀ p ∈ U,
      ∀ q ∈ U,
        ∀ b ∈ W,
          ∀ (hp : Nat.Prime p) (hq : Nat.Prime q),
            @legendreSym p ⟨hp⟩ (b : ℤ) = @legendreSym q ⟨hq⟩ (b : ℤ) := by
    intro p hp q hq b hb hpP hqP
    exact
      hQpair p ((Finset.mem_erase.mp (hUQ hp)).2) q ((Finset.mem_erase.mp (hUQ hq)).2) b hb hpP hqP
  have hpass :=
    strongMillerRabinPass_all_of_signature_class (Q := U) (K := k * L) W hprimeU hUcard hUorder
      hUproductMod hmod4U hbase hnotdivU hpairU
  exact ⟨U, fun p hp => hQP ((Finset.mem_erase.mp (hUQ hp)).2), hUcard, hUcar, hpass⟩

end PseudoPrime.PrimeTest.MillerRabin.AGP
