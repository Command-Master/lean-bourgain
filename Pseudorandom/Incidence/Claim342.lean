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

lemma claim_342 (β : ℝ) (h : 0 < β) (P : Finset (α × α)) (L : Finset (Line α)) (n : ℕ+)
  (h₁ : P.card ≤ n) (h₂ : L.card ≤ n) (nh :
    (Intersections P L).card > (ST_C₅ * n ^ (3/2 - ST_prime_field_eps₃ β) : ℝ))
    (hd : ∀ l ∈ P, (IntersectionsL l L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)) :
  ∃ p₁ ∈ P, ∃ p₂ ∈ P, p₁ ≠ p₂ ∧ (P.filter (fun x => (∃ l ∈ L, x ∈ l ∧ p₁ ∈ l) ∧ (∃ l ∈ L, x ∈ l ∧ p₂ ∈ l))).card > (ST_C₆ * n ^ (1 - ST_prime_field_eps₄ β) : ℝ) := by
  -- try {
  have pne : P.Nonempty := by
    by_contra! pe
    simp only [not_nonempty_iff_eq_empty] at pe
    simp only [pe, card_empty, zero_le, Int_empty, CharP.cast_eq_zero, gt_iff_lt, ne_eq,
      not_mem_empty, IsEmpty.forall_iff, Prod.forall, forall_const, filter_true_of_mem, ite_self,
      expect_const_zero] at *
    suffices 0 ≤ (ST_C₅ * n ^ (3/2 - ST_prime_field_eps₃ β) : ℝ) by linarith
    apply mul_nonneg
    simp only [NNReal.zero_le_coe]
    apply rpow_nonneg
    simp only [Nat.cast_nonneg]
  have lne : L.Nonempty := by
    -- sorry
    by_contra! le
    simp only [not_nonempty_iff_eq_empty] at le
    simp only [le, card_empty, zero_le, Int2_empty, CharP.cast_eq_zero, gt_iff_lt, ne_eq,
      not_mem_empty, IsEmpty.forall_iff, Prod.forall, forall_const, filter_true_of_mem, ite_self,
      expect_const_zero] at *
    suffices 0 ≤ (ST_C₅ * n ^ (3/2 - ST_prime_field_eps₃ β) : ℝ) by linarith
    apply mul_nonneg
    simp only [NNReal.zero_le_coe]
    apply rpow_nonneg
    simp only [Nat.cast_nonneg]
  suffices 𝔼 (p₁ ∈ P) (p₂ ∈ P),
      (if p₁ ≠ p₂ then (P.filter (fun x => (∃ l ∈ L, x ∈ l ∧ p₁ ∈ l) ∧ (∃ l ∈ L, x ∈ l ∧ p₂ ∈ l))).card else 0)
      > (ST_C₆ * n ^ (1 - ST_prime_field_eps₄ β) : ℝ) by
    -- sorry
    by_contra! v
    suffices 𝔼 (p₁ ∈ P) (p₂ ∈ P),
        (if p₁ ≠ p₂ then (P.filter (fun x => (∃ l ∈ L, x ∈ l ∧ p₁ ∈ l) ∧ (∃ l ∈ L, x ∈ l ∧ p₂ ∈ l))).card else 0)
        ≤ (ST_C₆ * n ^ (1 - ST_prime_field_eps₄ β) : ℝ) by
      linarith
    apply Finset.expect_le
    simp only [nonempty_product, and_self]
    assumption
    simp only [mem_product]
    intros x h
    split
    rename x.1 ≠ x.2 => hneq
    apply v x.1 h.1 x.2 h.2 hneq
    apply mul_nonneg
    simp only [NNReal.zero_le_coe]
    apply rpow_nonneg
    simp only [Nat.cast_nonneg]
  calc (𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then (P.filter (fun x => (∃ l ∈ L, x ∈ l ∧ p₁ ∈ l) ∧ (∃ l ∈ L, x ∈ l ∧ p₂ ∈ l))).card else 0) : ℝ)
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then ∑ q ∈ P, (if (∃ l ∈ L, q ∈ l ∧ p₁ ∈ l) ∧ (∃ l ∈ L, q ∈ l ∧ p₂ ∈ l) then 1 else 0) else 0) := by
      rcongr
      simp only [ne_eq, ite_not, sum_boole]
    _ ≥ 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then ∑ q ∈ P \ {p₁, p₂}, (if (∃ l ∈ L, q ∈ l ∧ p₁ ∈ l) ∧ (∃ l ∈ L, q ∈ l ∧ p₂ ∈ l) then 1 else 0) else 0) := by
      gcongr
      simp only [ne_eq, sum_boole, ite_not]
      split
      simp only [le_refl]
      norm_cast
      apply card_le_card
      apply filter_subset_filter
      simp only [sdiff_subset]
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then ∑ q ∈ P \ {p₁, p₂}, (if ∃ l ∈ L, q ∈ l ∧ p₁ ∈ l then 1 else 0) * (if ∃ l ∈ L, q ∈ l ∧ p₂ ∈ l then 1 else 0) else 0) := by
      rcongr
      simp [-sum_boole]
      congr
      ext
      split
      any_goals split
      any_goals split
      all_goals simp_all
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then ∑ q ∈ P \ {p₁, p₂}, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card else 0) := by
      rcongr x
      simp [-mul_ite, -ite_mul]
      split
      rfl
      apply sum_congr
      rfl
      intro q hq
      congr
      norm_cast
      apply exists_eq_card_filter_of_card_le_one
      calc (L.filter (fun l => q ∈ l ∧ x.1 ∈ l)).card
        _ ≤ (univ.filter (fun (l : Line α) => q ∈ l ∧ x.1 ∈ l)).card := by apply card_le_card; apply filter_subset_filter; simp
        _ = 1 := by apply point_intersect; intro v; simp_all
      norm_cast
      apply exists_eq_card_filter_of_card_le_one
      calc (L.filter (fun l => q ∈ l ∧ x.2 ∈ l)).card
        _ ≤ (univ.filter (fun (l : Line α) => q ∈ l ∧ x.2 ∈ l)).card := by apply card_le_card; apply filter_subset_filter; simp
        _ = 1 := by apply point_intersect; intro v; simp_all
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then
        (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - ∑ q ∈ {p₁, p₂}, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card
        else 0) := by
      apply expect_congr
      rfl
      intro x hx
      simp only [ne_eq, ite_not, Nat.cast_sum, Nat.cast_mul]
      split
      rfl
      rw [sum_sdiff_eq_sub]
      simp only [mem_product] at hx
      rw [subset_iff]
      intro v vh
      simp_all only [gt_iff_lt,
        one_div,
        Prod.forall,
        mem_insert,
        mem_singleton]
      unhygienic
        with_reducible
          aesop_destruct_products
      simp_all only [Prod.mk.injEq,
        not_and]
      unhygienic
        aesop_cases
          vh
      ·
        simp_all only
      ·
        simp_all only
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then
        (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - ((L.filter (fun l => p₁ ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => p₁ ∈ l ∧ p₂ ∈ l)).card +
        (L.filter (fun l => p₂ ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => p₂ ∈ l ∧ p₂ ∈ l)).card
        )
        else 0) := by
      apply expect_congr
      rfl
      intro x hx
      simp only []
      split
      congr
      rw [sum_pair]
      norm_cast
      assumption
      rfl
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then
        (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - ((L.filter (fun l => p₁ ∈ l)).card * (L.filter (fun l => p₁ ∈ l ∧ p₂ ∈ l)).card +
        (L.filter (fun l => p₂ ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => p₂ ∈ l)).card
        )
        else 0) := by simp
    _  ≥ 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then
        (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - ((L.filter (fun l => p₁ ∈ l)).card * 1 + 1 * (L.filter (fun l => p₂ ∈ l)).card)
        else 0) := by
      rw [ge_iff_le]
      apply expect_le_expect
      intro x hx
      simp only []
      split
      gcongr
      norm_cast
      calc (L.filter (fun l => x.1 ∈ l ∧ x.2 ∈ l)).card
        _ ≤ (univ.filter (fun (l : Line α) => x.1 ∈ l ∧ x.2 ∈ l)).card := by apply card_le_card; apply filter_subset_filter; simp
        _ = 1 := by apply point_intersect; assumption
      norm_cast
      calc (L.filter (fun l => x.2 ∈ l ∧ x.1 ∈ l)).card
        _ ≤ (univ.filter (fun (l : Line α) => x.2 ∈ l ∧ x.1 ∈ l)).card := by apply card_le_card; apply filter_subset_filter; simp
        _ = 1 := by apply point_intersect; apply Ne.symm; assumption
      simp only [le_refl]
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then
        (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - ((IntersectionsL p₁ L).card + (IntersectionsL p₂ L).card) else 0) := by simp only [one_mul, mul_one, IntersectionsL]
    _ ≥ 𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ ≠ p₂ then
        (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) else 0) := by
      gcongr
      split
      split
      gcongr
      apply hd
      simp_all only [gt_iff_lt, one_div, Prod.forall, mem_product, ne_eq]
      apply hd
      simp_all only [gt_iff_lt, one_div, Prod.forall, mem_product, ne_eq]
      simp only [le_refl]
    _ ≥ 𝔼 (p₁ ∈ P) (p₂ ∈ P), ((∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) - (if p₁ = p₂ then
          (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card) else 0)
         ) := by
      rw [ge_iff_le]
      apply expect_le_expect
      intros
      split
      split
      simp_all only [gt_iff_lt, one_div, Prod.forall, mem_product, and_self, Nat.cast_sum,
        Nat.cast_mul, sub_sub_cancel_left, neg_add_rev, ne_eq, not_true_eq_false, ite_false,
        add_self_nonpos_iff, Left.neg_nonpos_iff, Nat.ofNat_pos, mul_nonneg_iff_of_pos_left]
      apply rpow_nonneg
      simp only [Nat.cast_nonneg]
      simp only [Nat.cast_sum, Nat.cast_mul, one_div, CharP.cast_eq_zero, sub_zero, le_refl]
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - 𝔼 (p₁ ∈ P) (p₂ ∈ P), (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        𝔼 (p₁ ∈ P) (p₂ ∈ P), (if p₁ = p₂ then (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card) else 0)
         := by
      simp only [Nat.cast_sum, Nat.cast_mul, one_div, Nat.cast_ite, CharP.cast_eq_zero,
        expect_sub_distrib]
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        𝔼 (p₁ ∈ P), 𝔼 (p₂ ∈ P), (if p₁ = p₂ then (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card) else 0 : ℝ) := by
      congr 1
      congr 1
      rw [expect_const]
      simp only [nonempty_product, pne, and_self]
      rw [expect_product' (s := P) (t := P)
        (f := fun p₁ p₂ => (if p₁ = p₂ then (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card) else 0 : ℝ))]
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (P.card : ℝ)⁻¹ * 𝔼 (p₁ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card^2 : ℝ) := by
      congr 1
      rw [mul_expect]
      apply expect_congr
      rfl
      intro p₁ hp₁
      rw [expect_eq_single_of_mem p₁]
      rw [←nnratCast_smul_eq_nnqsmul ℝ]
      simp only [NNRat.cast_inv, NNRat.cast_natCast, ↓reduceIte, smul_eq_mul, sq]
      exact hp₁
      intros
      split
      simp_all only [gt_iff_lt, one_div, Prod.forall, ne_eq, not_true_eq_false]
      rfl
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (P.card : ℝ)⁻¹ * 𝔼 (p₁ ∈ P), (∑ q ∈ P \ {p₁}, ((L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card^2 : ℝ) + (L.filter (fun l => p₁ ∈ l)).card^2 : ℝ) := by
      congr 2
      apply expect_congr
      rfl
      intro p₁ hp₁
      rw [Finset.sum_eq_sum_diff_singleton_add (i := p₁)]
      simp only [and_self]
      assumption
    _ ≥ 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (P.card : ℝ)⁻¹ * 𝔼 (p₁ ∈ P), (∑ q ∈ P \ {p₁}, (1^2 : ℝ) + (IntersectionsL p₁ L).card^2 : ℝ) := by
      gcongr with i hi j hj
      norm_cast
      calc (L.filter (fun l => j ∈ l ∧ i ∈ l)).card
        _ ≤ (univ.filter (fun (l : Line α) => j ∈ l ∧ i ∈ l)).card := by apply card_le_card; apply filter_subset_filter; simp
        _ = 1 := by apply point_intersect; intro v; simp only [v, mem_sdiff, mem_singleton,
          not_true_eq_false, and_false] at hj
      simp only [IntersectionsL, Subset.refl]
    _ ≥ 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (P.card : ℝ)⁻¹ * 𝔼 (p₁ ∈ P), (P.card + (4 * n^(1 / 2 + 2 * ST_prime_field_eps₂ β))^2 : ℝ) := by
      gcongr
      simp only [one_pow, sum_const, nsmul_eq_mul, mul_one, Nat.cast_le]
      apply card_le_card
      simp only [sdiff_subset]
      apply hd
      assumption
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (1 + (P.card : ℝ)⁻¹ * (4 * n^(1 / 2 + 2 * ST_prime_field_eps₂ β))^2) := by
      congr
      rw [expect_const]
      ring_nf
      congr
      apply mul_inv_cancel
      simp only [ne_eq, Nat.cast_eq_zero, card_eq_zero]
      intro v
      simp_all only [card_empty, zero_le, Int_empty, CharP.cast_eq_zero, gt_iff_lt, not_mem_empty,
        one_div, IsEmpty.forall_iff, Prod.forall, forall_const, Finset.not_nonempty_empty]
      exact pne
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (1 + (P.card : ℝ)⁻¹ * (16 * n^(1 + 4 * ST_prime_field_eps₂ β))) := by
      congr
      rw [mul_pow, ←rpow_nat_cast, ←rpow_nat_cast, ←rpow_mul]
      norm_num
      congr
      ring
      simp only [Nat.cast_nonneg]
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (1 + ((4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)⁻¹ * (P.card * (4 * n^(1/2 + 2*ST_prime_field_eps₂ β))) : ℝ)⁻¹ * (16 * n^(1 + 4 * ST_prime_field_eps₂ β))) := by
      congr
      ring_nf
      rw [mul_inv_cancel]
      ring
      simp only [one_div, ne_eq, Nat.cast_nonneg]
      rw [Real.rpow_eq_zero]
      simp only [Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true]
      simp only [Nat.cast_nonneg]
      suffices 2⁻¹ + 2 * ST_prime_field_eps₂ β > 0 by linarith
      have : (2 : ℝ)⁻¹ > 0 := by norm_num
      have : ST_prime_field_eps₂ β > 0 := by apply pos_ST_prime_field_eps₂; assumption
      linarith
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (1 + ((4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)⁻¹ * ∑ x ∈ P, 4 * (n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))⁻¹ * (16 * n^(1 + 4 * ST_prime_field_eps₂ β))) := by
      congr
      simp only [one_div, sum_const, nsmul_eq_mul]
    _ ≥ 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (1 + ((4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)⁻¹ * (Intersections P L).card : ℝ)⁻¹ * (16 * n^(1 + 4 * ST_prime_field_eps₂ β))) := by
      gcongr
      apply mul_pos
      simp only [one_div, mul_inv_rev, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_right]
      apply rpow_pos_of_pos
      simp only [Nat.cast_pos, PNat.pos]
      calc
        (0 : ℝ) ≤ (ST_C₅ * n ^ (3 / 2 - ST_prime_field_eps₃ β) : ℝ) := by apply mul_nonneg; simp; apply rpow_nonneg; simp
        _ < (Intersections P L).card := by assumption
      rw [IntersectionsL_sum, Nat.cast_sum]
      apply sum_le_sum
      exact hd
    _ > 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (1 + ((4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ)⁻¹ * (ST_C₅ * n ^ (3 / 2 - ST_prime_field_eps₃ β)) : ℝ)⁻¹ * (16 * n^(1 + 4 * ST_prime_field_eps₂ β))) := by
      gcongr
      simp only [gt_iff_lt, Nat.ofNat_pos, mul_pos_iff_of_pos_left]
      apply rpow_pos_of_pos
      simp only [Nat.cast_pos, PNat.pos]
      apply mul_pos
      simp only [one_div, mul_inv_rev, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_right]
      apply rpow_pos_of_pos
      simp only [Nat.cast_pos, PNat.pos]
      apply mul_pos
      exact ST_C₅_pos
      apply rpow_pos_of_pos
      simp only [Nat.cast_pos, PNat.pos]
      simp only [one_div, mul_inv_rev, gt_iff_lt, inv_pos, Nat.ofNat_pos, mul_pos_iff_of_pos_right]
      apply rpow_pos_of_pos
      simp only [Nat.cast_pos, PNat.pos]
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) + 4 * n^(1/2 + 2*ST_prime_field_eps₂ β)) -
        (1 + 4 * ST_C₅⁻¹ * n ^ (2*ST_prime_field_eps₂ β + ST_prime_field_eps₃ β - 1) * (16 * n^(1 + 4 * ST_prime_field_eps₂ β))) := by
      congr 3
      simp only [one_div, mul_inv_rev, inv_inv, NNReal.coe_inv]
      ring_nf
      congr 1
      rw [mul_comm, ←mul_assoc, mul_comm]
      congr
      simp only [one_div, Nat.cast_nonneg, ← rpow_neg, neg_sub, Nat.cast_pos, PNat.pos, ← rpow_add]
      congr 1
      ring
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (2*ST_prime_field_eps₂ β + ST_prime_field_eps₃ β - 1) * n^(1 + 4 * ST_prime_field_eps₂ β)) := by
      ring
    _ = 𝔼 (p₁ ∈ P) (p₂ ∈ P), (∑ q ∈ P, (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      simp only [one_div, NNReal.coe_inv, Nat.cast_pos, PNat.pos, ← rpow_add, sub_right_inj,
        mul_eq_mul_left_iff, mul_eq_zero, OfNat.ofNat_ne_zero, inv_eq_zero, NNReal.coe_eq_zero,
        false_or]
      left
      congr 1
      ring
    _ = (∑ q ∈ P, 𝔼 (p₁ ∈ P) (p₂ ∈ P), (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card * (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card)
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      rw [Finset.expect_sum_comm]
    _ = (∑ q ∈ P, (𝔼 (p₁ ∈ P), (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card : ℝ) * (𝔼 (p₂ ∈ P), (L.filter (fun l => q ∈ l ∧ p₂ ∈ l)).card : ℝ))
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      simp only [one_div, NNReal.coe_inv, sub_left_inj]
      rcongr
      rw [expect_mul_expect, ←expect_product']
    _ = (∑ q ∈ P, (𝔼 (p₁ ∈ P), (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card : ℝ)^2)
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      simp only [one_div, NNReal.coe_inv, sq]
    _ ≥ (P.card : ℝ)⁻¹ * (∑ q ∈ P, (𝔼 (p₁ ∈ P), (L.filter (fun l => q ∈ l ∧ p₁ ∈ l)).card : ℝ))^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      gcongr
      rw [inv_mul_le_iff]
      apply sq_sum_le_card_mul_sum_sq
      simp only [Nat.cast_pos, card_pos, pne]
    _ = (P.card : ℝ)⁻¹ * (∑ q ∈ P, (𝔼 (p₁ ∈ P), ∑ l ∈ L, (if q ∈ l ∧ p₁ ∈ l then 1 else 0)))^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      rcongr
      simp only [sum_boole]
    _ = (P.card : ℝ)⁻¹ * (∑ q ∈ P, ((P.card : ℝ)⁻¹ * ∑ p₁ ∈ P, ∑ l ∈ L, (if q ∈ l ∧ p₁ ∈ l then 1 else 0)))^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      rcongr
      simp only [expect, sum_boole]
      rw [←nnratCast_smul_eq_nnqsmul ℝ]
      simp only [NNRat.cast_inv, NNRat.cast_natCast, smul_eq_mul]
    _ = (P.card^3 : ℝ)⁻¹ * (∑ q ∈ P, (∑ p₁ ∈ P, ∑ l ∈ L, (if q ∈ l ∧ p₁ ∈ l then 1 else 0)))^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      simp only [sum_boole, ← mul_sum, one_div, NNReal.coe_inv, sub_left_inj]
      ring
    _ = (P.card^3 : ℝ)⁻¹ * (∑ l ∈ L, ∑ q ∈ P, ∑ p₁ ∈ P, (if q ∈ l ∧ p₁ ∈ l then 1 else 0))^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      conv =>
        rhs
        rw [sum_comm]
      congr
      ext q
      rw [sum_comm]
    _ = (P.card^3 : ℝ)⁻¹ * (∑ l ∈ L, ∑ q ∈ P, ∑ p₁ ∈ P, (if q ∈ l then 1 else 0) * (if p₁ ∈ l then 1 else 0))^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      rcongr
      rw [ite_zero_mul_ite_zero]
      simp only [mul_one]
    _ = (P.card^3 : ℝ)⁻¹ * (∑ l ∈ L, (∑ q ∈ P, if q ∈ l then 1 else 0) * (∑ p₁ ∈ P, if p₁ ∈ l then 1 else 0))^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      rcongr
      rw [sum_mul_sum]
    _ = (P.card^3 : ℝ)⁻¹ * (∑ l ∈ L, (∑ q ∈ P, if q ∈ l then 1 else 0)^2)^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      simp only [sum_boole, sq, one_div, NNReal.coe_inv]
    _ ≥ (P.card^3 : ℝ)⁻¹ * ((L.card : ℝ)⁻¹ * (∑ l ∈ L, (∑ q ∈ P, if q ∈ l then 1 else 0))^2)^2
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      gcongr
      rw [inv_mul_le_iff]
      apply sq_sum_le_card_mul_sum_sq
      simp only [Nat.cast_pos, card_pos, lne]
    _ = (P.card^3 : ℝ)⁻¹ * (L.card^2 : ℝ)⁻¹ * ((∑ l ∈ L, (∑ q ∈ P, if q ∈ l then 1 else 0)))^4
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      ring
    _ = (P.card^3 : ℝ)⁻¹ * (L.card^2 : ℝ)⁻¹ * ((∑ l ∈ L, (IntersectionsP P l).card))^4
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      simp only [sum_boole, one_div, NNReal.coe_inv, IntersectionsP, Nat.cast_sum]
    _ ≥ (n^3 : ℝ)⁻¹ * (n^2 : ℝ)⁻¹ * (ST_C₅ * n^(3/2 - ST_prime_field_eps₃ β))^4
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      gcongr
      rw [←IntersectionsP_sum]
      apply le_of_lt
      exact nh
    _ = ST_C₅^4 * ((n^5 : ℝ)⁻¹ * (n^(3/2 - ST_prime_field_eps₃ β))^4)
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      ring
    _ = ST_C₅^4 * n^(1 - 4*ST_prime_field_eps₃ β)
        - 8 * n^(1/2 + 2*ST_prime_field_eps₂ β) - 1 -
        64 * ST_C₅⁻¹ * (n ^ (ST_prime_field_eps₃ β + 6 * ST_prime_field_eps₂ β)) := by
      congr
      rw [←rpow_nat_cast, ←rpow_nat_cast, ←rpow_neg, ←rpow_mul, ←rpow_add]
      congr 1
      ring
      simp only [Nat.cast_pos, PNat.pos]
      simp only [Nat.cast_nonneg]
      simp only [Nat.cast_nonneg]
    _ ≥ ST_C₅^4 * n^(1 - 4*ST_prime_field_eps₃ β)
        - 8 * n^(1 - 4*ST_prime_field_eps₃ β) - n^(1 - 4*ST_prime_field_eps₃ β) -
        64 * 1 * n^(1 - 4*ST_prime_field_eps₃ β) := by
      gcongr
      norm_cast
      simp only [PNat.one_le]
      apply lemma1
      assumption
      apply Real.one_le_rpow
      norm_cast
      simp only [PNat.one_le]
      simp
      apply lemma2
      assumption
      norm_cast
      apply inv_le_one
      apply one_le_ST_C₅
      norm_cast
      simp only [PNat.one_le]
      apply lemma3
      assumption
    _ = (ST_C₅^4 - 73) * n^(1 - 4*ST_prime_field_eps₃ β) := by ring
    _ = (ST_C₆ * n ^ (1 - ST_prime_field_eps₄ β) : ℝ) := by
      congr 2
      simp [ST_C₅]
      rw [←rpow_nat_cast, ←rpow_mul]
      simp
      apply add_nonneg
      simp
      simp
      simp [ST_prime_field_eps₃]
      ring
  -- }
