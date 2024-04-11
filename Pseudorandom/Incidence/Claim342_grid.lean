import Mathlib.Data.Nat.Prime
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Prereqs.Expect.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.SetLike.Fintype
import Pseudorandom.Geometry.Lines
import Pseudorandom.Incidence.Constants
import Pseudorandom.Util

open Classical Real BigOps Finset

variable {α : Type*} [Field α] [Fintype α]

set_option maxHeartbeats 1000000

theorem claim342_grid (β : ℝ) (h : 0 < β) (A B : Finset α) (L : Finset (Line α)) (n : ℕ+)
  (hA : A.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)) (hB : B.card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  (h₂ : L.card ≤ n)
  (nHoriz : ∀ l ∈ L, ¬l.horiz)
  -- (hC : ∀ l ∈ L, (n ^ (1/2 - SG_eps β) : ℝ) < (IntersectionsP (A ×ˢ B) l).card)
  (nh : (SG_C₃ * n ^ (3/2 - SG_eps β) : ℝ) < (Intersections (A ×ˢ B) L).card) :
  ∃ b₁ ∈ B, ∃ b₂ ∈ B, b₁ ≠ b₂ ∧ (L.filter (fun l => (∃ p ∈ A ×ˢ {b₁}, p ∈ l) ∧ ∃ p ∈ A ×ˢ {b₂}, p ∈ l)).card > (SG_C₄ * n ^ (1 - SG_eps₂ β) : ℝ) := by
  have bne : B.Nonempty := by
    by_contra! pe
    simp only [not_nonempty_iff_eq_empty] at pe
    simp_all [Int_empty, Finset.product_empty]
    suffices 0 ≤ (SG_C₃ * n ^ (3/2 - SG_eps β) : ℝ) by linarith
    apply mul_nonneg
    simp only [NNReal.zero_le_coe]
    apply rpow_nonneg
    simp only [Nat.cast_nonneg]
  have lne : L.Nonempty := by
    by_contra! le
    simp only [not_nonempty_iff_eq_empty] at le
    simp only [le, card_empty, zero_le, Int2_empty, CharP.cast_eq_zero, gt_iff_lt, ne_eq,
      not_mem_empty, IsEmpty.forall_iff, Prod.forall, forall_const, filter_true_of_mem, ite_self,
      expect_const_zero] at *
    suffices 0 ≤ (SG_C₃ * n ^ (3/2 - SG_eps β) : ℝ) by linarith
    apply mul_nonneg
    simp only [NNReal.zero_le_coe]
    apply rpow_nonneg
    simp only [Nat.cast_nonneg]
  suffices 𝔼 (b₁ ∈ B) (b₂ ∈ B),
      (if b₁ ≠ b₂ then (L.filter (fun l => (∃ p ∈ A ×ˢ {b₁}, p ∈ l) ∧ ∃ p ∈ A ×ˢ {b₂}, p ∈ l)).card else 0)
      > (SG_C₄ * n ^ (1 - SG_eps₂ β) : ℝ) by
    by_contra! v
    suffices 𝔼 (b₁ ∈ B) (b₂ ∈ B),
      (if b₁ ≠ b₂ then (L.filter (fun l => (∃ p ∈ A ×ˢ {b₁}, p ∈ l) ∧ ∃ p ∈ A ×ˢ {b₂}, p ∈ l)).card else 0)
      ≤ (SG_C₄ * n ^ (1 - SG_eps₂ β) : ℝ) by linarith
    apply Finset.expect_le
    simp only [nonempty_product, and_self]
    assumption
    simp only [mem_product (s := B)]
    intros x h
    split
    rename x.1 ≠ x.2 => hneq
    apply v x.1 h.1 x.2 h.2 hneq
    apply mul_nonneg
    simp only [NNReal.zero_le_coe]
    apply rpow_nonneg
    simp only [Nat.cast_nonneg]
  calc (𝔼 (b₁ ∈ B) (b₂ ∈ B),
      (if b₁ ≠ b₂ then (L.filter (fun l => (∃ p ∈ A ×ˢ {b₁}, p ∈ l) ∧ ∃ p ∈ A ×ˢ {b₂}, p ∈ l)).card else 0) : ℝ)
    _ = 𝔼 (b₁ ∈ B) (b₂ ∈ B),
      (if b₁ ≠ b₂ then (L.filter (fun l => (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l)).card else 0) := by simp
    _ = 𝔼 (b₁ ∈ B) (b₂ ∈ B),
      (if b₁ ≠ b₂ then ∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) else 0) := by simp
    _ = 𝔼 (b₁ ∈ B) (b₂ ∈ B),
      (∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) -
        (if b₁ = b₂ then ∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) else 0)) := by
      simp only [ne_eq, sum_boole, ite_not]
      rcongr
      split <;> simp only [sub_self, sub_zero]
    _ = 𝔼 (b₁ ∈ B) (b₂ ∈ B), ∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) -
        𝔼 (b₁ ∈ B) (b₂ ∈ B),  (if b₁ = b₂ then ∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) else 0) := by
      simp only [expect_sub_distrib]
    _ = 𝔼 (b₁ ∈ B) (b₂ ∈ B), ∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) -
        𝔼 (b₁ ∈ B), (B.card : ℝ)⁻¹ * ∑ l ∈ L, (if ∃ a ∈ A, (a, b₁) ∈ l then 1 else 0) := by
      congr 1
      simp only
      rw [expect_product' (s := B) (t := B) (f := fun b₁ b₂ => ((if b₁ = b₂ then ∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) else 0) : ℝ))]
      apply expect_congr
      rfl
      intro x hx
      rw [expect_eq_single_of_mem x hx]
      simp only [↓reduceIte, and_self, sum_boole, ← nnratCast_smul_eq_nnqsmul ℝ, NNRat.cast_inv,
        NNRat.cast_natCast, smul_eq_mul]
      intro j hj
      simp_all only [one_div, ne_eq, and_self, sum_boole, ite_eq_right_iff, Nat.cast_eq_zero, card_eq_zero]
      intros
      tauto
    _ ≥ 𝔼 (b₁ ∈ B) (b₂ ∈ B), ∑ l ∈ L, (if (∃ a ∈ A, (a, b₁) ∈ l) ∧ ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) -
        𝔼 (b₁ ∈ B), (B.card : ℝ)⁻¹ * L.card := by
      gcongr
      simp only [sum_boole, Nat.cast_le]
      gcongr
      simp only [filter_subset]
    _ = 𝔼 (b₁ ∈ B) (b₂ ∈ B), ∑ l ∈ L, (if ∃ a ∈ A, (a, b₁) ∈ l then 1 else 0)*(if ∃ a ∈ A, (a, b₂) ∈ l then 1 else 0) -
        (B.card : ℝ)⁻¹ * L.card := by
      rcongr
      simp only [sum_boole, ite_zero_mul_ite_zero, mul_one]
      simp only [expect_const bne]
    _ = 𝔼 (b₁ ∈ B) (b₂ ∈ B), ∑ l ∈ L, (A.filter (fun a => (a, b₁) ∈ l)).card*(A.filter (fun a => (a, b₂) ∈ l)).card -
        (B.card : ℝ)⁻¹ * L.card := by
      rcongr p
      simp only
      apply sum_congr
      rfl
      intro x xl
      norm_cast
      congr
      repeat {
      apply exists_eq_card_filter_of_card_le_one
      by_contra! nh
      rw [Finset.one_lt_card] at nh
      have ⟨a, ha, b, hb, neq⟩ := nh
      simp only [filter_congr_decidable, mem_filter] at ha
      simp only [filter_congr_decidable, mem_filter] at hb
      try
        have := line_eq_of (a, p.1) (b, p.1) (by aesop) x ⟨ha.2, hb.2⟩
      try
        have := line_eq_of (a, p.2) (b, p.2) (by aesop) x ⟨ha.2, hb.2⟩
      have xhoriz : x.horiz := by
        rw [this]
        rw [Line.of_horiz_iff]
      exact nHoriz x xl xhoriz
      }
    _ = ∑ l ∈ L, 𝔼 (b₁ ∈ B) (b₂ ∈ B), (A.filter (fun a => (a, b₁) ∈ l)).card*(A.filter (fun a => (a, b₂) ∈ l)).card -
        (B.card : ℝ)⁻¹ * L.card := by
      rw [expect_sum_comm]
    _ = ∑ l ∈ L, (𝔼 (b₁ ∈ B), ((A.filter (fun a => (a, b₁) ∈ l)).card : ℝ))* (𝔼 (b₂ ∈ B), ((A.filter (fun a => (a, b₂) ∈ l)).card : ℝ)) -
        (B.card : ℝ)⁻¹ * L.card := by
      rcongr l
      simp only
      simp [expect_product' (s := B) (t := B) (f := fun b₁ b₂ => ((A.filter (fun a => (a, b₁) ∈ l)).card*(A.filter (fun a => (a, b₂) ∈ l)).card : ℝ)),
        expect_mul_expect]
    _ = ∑ l ∈ L, (𝔼 (b₁ ∈ B), ((A.filter (fun a => (a, b₁) ∈ l)).card : ℝ))^2 -
        (B.card : ℝ)⁻¹ * L.card := by simp only [sq]
    _ ≥ (L.card : ℝ)⁻¹ * (∑ l ∈ L, 𝔼 (b₁ ∈ B), ((A.filter (fun a => (a, b₁) ∈ l)).card : ℝ))^2 -
        (B.card : ℝ)⁻¹ * L.card := by
      gcongr
      rw [inv_mul_le_iff]
      norm_cast
      apply sq_sum_le_card_mul_sum_sq
      norm_cast
      rw [Finset.card_pos]
      exact lne
    _ = (L.card : ℝ)⁻¹ * ((B.card : ℝ)⁻¹ * ∑ l ∈ L, ∑ (b₁ ∈ B), (A.filter (fun a => (a, b₁) ∈ l)).card)^2 -
        (B.card : ℝ)⁻¹ * L.card := by
      simp [expect, ←nnratCast_smul_eq_nnqsmul ℝ, mul_sum]
    _ = (L.card : ℝ)⁻¹ * ((B.card : ℝ)⁻¹ * ∑ l ∈ L, ((A ×ˢ B).filter (fun x => x ∈ l)).card)^2 -
        (B.card : ℝ)⁻¹ * L.card := by
      rcongr
      norm_cast
      rcongr
      conv =>
        lhs
        rhs
        intro
        rw [Finset.card_filter]
      rw [Finset.sum_comm]
      rw [←Finset.sum_product']
      simp
    _ = (L.card : ℝ)⁻¹ * ((B.card : ℝ)⁻¹ * ∑ l ∈ L, (IntersectionsP (A ×ˢ B) l).card)^2 -
        (B.card : ℝ)⁻¹ * L.card := rfl
    _ = (L.card : ℝ)⁻¹ * ((B.card : ℝ)⁻¹ * (Intersections (A ×ˢ B) L).card)^2 -
        (B.card : ℝ)⁻¹ * L.card := by simp [IntersectionsP_sum]
    _ ≥ (n : ℝ)⁻¹ * ((4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)⁻¹ * (Intersections (A ×ˢ B) L).card)^2 -
        (B.card : ℝ)⁻¹ * n := by
      gcongr
    _ > (n : ℝ)⁻¹ * ((4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ)⁻¹ * (SG_C₃ * n ^ (3/2 - SG_eps β)))^2 -
        (B.card : ℝ)⁻¹ * n := by
      gcongr
      simp
      simp [rpow_pos_of_pos]
    _ = SG_C₃^2 * 16⁻¹ * (n^(-1 : ℝ) * ((n^(-1/2 - 2*ST_prime_field_eps β) : ℝ) * n ^ (3/2 - SG_eps β))^2) -
        (B.card : ℝ)⁻¹ * n := by simp [rpow_neg_one, ←rpow_neg]; ring_nf
    _ = SG_C₃^2 * 16⁻¹ * (n^(-1 : ℝ) * (n^(-1/2 - 2*ST_prime_field_eps β + (3/2 - SG_eps β)))^2) -
        (B.card : ℝ)⁻¹ * n := by simp [←rpow_add]
    _ = SG_C₃^2 * 16⁻¹ * (n^(-1 : ℝ) * n^((-1/2 - 2*ST_prime_field_eps β + (3/2 - SG_eps β)) * 2)) -
        (B.card : ℝ)⁻¹ * n := by simp only [←rpow_nat_cast (n := 2)]; rw [←rpow_mul]; congr; simp only [Nat.cast_nonneg]
    _ = SG_C₃^2 * 16⁻¹ * n^(-1 + (-1/2 - 2*ST_prime_field_eps β + (3/2 - SG_eps β)) * 2) -
        (B.card : ℝ)⁻¹ * n := by rw [←rpow_add]; simp
    _ = SG_C₃^2 * 16⁻¹ * n^(1 - 4*ST_prime_field_eps β - 2 * SG_eps β) -
        (B.card : ℝ)⁻¹ * n := by ring_nf
    _ > SG_C₃^2 * 16⁻¹ * n^(1 - 4*ST_prime_field_eps β - 2 * SG_eps β) -
        (SG_C₃ * n ^ (1/2 - SG_eps β) : ℝ)⁻¹ * n := by
      gcongr
      simp
      apply mul_pos
      exact SG_C₃_pos
      apply rpow_pos_of_pos
      simp
      calc (SG_C₃ * n ^ (1/2 - SG_eps β) : ℝ)
        _ = (n : ℝ)⁻¹ * SG_C₃ * (n ^ (1/2 - SG_eps β) * n) := by ring_nf; simp
        _ = (n : ℝ)⁻¹ * SG_C₃ * n ^ ((1/2 - SG_eps β) + 1) := by simp [rpow_add_one]
        _ = (n : ℝ)⁻¹ * (SG_C₃ * n ^ (3/2 - SG_eps β)) := by ring_nf
        _ < (n : ℝ)⁻¹ * (Intersections (A ×ˢ B) L).card := by gcongr; simp
        _ = (n : ℝ)⁻¹ * ∑ l ∈ L, (IntersectionsP (A ×ˢ B) l).card := by simp [IntersectionsP_sum]
        _ = (n : ℝ)⁻¹ * ∑ l ∈ L, ∑ p ∈ (A ×ˢ B), (if p ∈ l then 1 else 0) := by simp [IntersectionsP]
        _ = (n : ℝ)⁻¹ * ∑ l ∈ L, ∑ b ∈ B, ∑ a ∈ A, (if (a, b) ∈ l then 1 else 0) := by simp [Finset.sum_product_right (s := A) (t := B)]
        _ ≤ (n : ℝ)⁻¹ * ∑ l ∈ L, ∑ b ∈ B, 1 := by
          gcongr with l hl ob
          simp
          rw [←exists_eq_card_filter_of_card_le_one]
          split <;> decide
          by_contra! nh
          rw [Finset.one_lt_card] at nh
          have ⟨a, ha, b, hb, neq⟩ := nh
          simp only [filter_congr_decidable, mem_filter] at ha
          simp only [filter_congr_decidable, mem_filter] at hb
          have := line_eq_of (a, ob) (b, ob) (by aesop) l ⟨ha.2, hb.2⟩
          have xhoriz : l.horiz := by
            rw [this]
            rw [Line.of_horiz_iff]
          exact nHoriz l hl xhoriz
        _ = ((n : ℝ)⁻¹ * L.card) * B.card := by simp; ring
        _ ≤ ((n : ℝ)⁻¹ * n) * B.card := by gcongr
        _ = B.card := by simp
    _ = SG_C₃^2 * 16⁻¹ * n^(1 - 4*ST_prime_field_eps β - 2 * SG_eps β) -
        SG_C₃⁻¹ * (n ^ (-1/2 + SG_eps β) * n) := by
      simp [←rpow_neg]
      ring_nf
    _ = SG_C₃^2 * 16⁻¹ * n^(1 - 4*ST_prime_field_eps β - 2 * SG_eps β) -
        SG_C₃⁻¹ * (n ^ ((-1/2 + SG_eps β) + 1)) := by simp [rpow_add_one]
    _ ≥ SG_C₃^2 * 16⁻¹ * n^(1 - 4*ST_prime_field_eps β - 2 * SG_eps β) -
        1 * n ^ (1 - 4*ST_prime_field_eps β - 2 * SG_eps β) := by
      gcongr
      apply inv_le_one
      norm_cast
      exact one_le_SG_C₃
      norm_cast
      simp
      ring_nf
      apply lemma7
    _ = (SG_C₃^2 * 16⁻¹ - 1) * n^(1 - 4*ST_prime_field_eps β - 2 * SG_eps β) := by ring
    _ = SG_C₄ * n ^ (1 - SG_eps₂ β) := by
      congr 2
      simp [SG_C₃, -coe_sqrt, mul_pow]
      rw [←NNReal.coe_pow]
      simp
      ring
      simp [ST_prime_field_eps, ST_prime_field_eps₂, ST_prime_field_eps₃, SG_eps]
      ring_nf
