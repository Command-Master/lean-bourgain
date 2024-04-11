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
import Mathlib.Combinatorics.Additive.Energy
import Mathlib.Combinatorics.Additive.PluenneckeRuzsa
import Mathlib.Combinatorics.Additive.RuzsaCovering
import LeanAPAP.Mathlib.Combinatorics.Additive.Energy

open NNRat Classical Real BigOps Finset Pointwise

variable {α : Type*} [Fintype α] [DecidableEq α]
  (A B C : Finset α)

lemma sub_le_add [AddCommGroup α] : (A - B).card ≤ ((A + B).card^3 / (A.card * B.card) : ℚ) := by
  by_cases A.Nonempty
  by_cases B.card ≠ 0
  calc ((A - B).card : ℚ≥0)
    _ = ((A - B).card * B.card) / B.card := by field_simp
    _ ≤ ((A + B).card * (B + B).card) / B.card := by
      gcongr ?a / _
      norm_cast
      apply card_sub_mul_le_card_add_mul_card_add
    _ = ((A + B).card * (2 • B).card) / B.card := by rw [two_smul]
    _ ≤ ((A + B).card * (((A+B).card / A.card)^2 * A.card)) / B.card := by
        gcongr
        apply card_nsmul_le
        assumption
    _ = (A + B).card^3 / (A.card * B.card) := by field_simp; ring_nf
  · simp_all
  · simp_all

lemma card_of_inv [GroupWithZero α] (a : α) (h : a ≠ 0) : (a • A).card = A.card := by
  apply Eq.symm
  apply card_congr (fun x _ => a * x)
  · intros a ha
    simp [mem_smul_finset]
    exists a
    simp [ha]
  · intros a b _ _ e
    simp_all
  · intros a ha
    simp [mem_smul_finset] at ha
    have ⟨y, hy⟩ := ha
    exists y
    simp
    assumption


lemma neg_inter_distrib [InvolutiveNeg α] : (-A ∩ -B) = -(A ∩ B) := by
  ext x
  simp

lemma add_smul_subset_smul_add_smul [CommSemiring α] (a b : α) : (a + b) • A ⊆ a • A + b • A := by
  rw [subset_iff]
  intro x hx
  rw [mem_smul_finset] at hx
  have ⟨y, hy, hx⟩ := hx
  rw [add_smul] at hx
  rw [← hx]
  simp only [add_mem_add, smul_mem_smul_finset, hy]

lemma sub_smul_subset_smul_sub_smul [CommRing α] (a b : α) : (a - b) • A ⊆ a • A - b • A := by
  rw [subset_iff]
  intro x hx
  rw [mem_smul_finset] at hx
  have ⟨y, hy, hx⟩ := hx
  rw [sub_smul] at hx
  rw [← hx]
  simp only [sub_mem_sub, smul_mem_smul_finset, hy]

lemma add_of_large_intersection [AddCommGroup α] (h : (A ∩ C).Nonempty) : (B+C).card ≤ ((B + A).card * (C+C).card / (A ∩ C).card : ℚ) := by
  calc
    ((B+C).card : ℚ≥0) = (B+C).card * (A ∩ C).card / (A ∩ C).card := by field_simp
    _ ≤ ((B + (A ∩ C)).card * ((A ∩ C) + C).card) / (A ∩ C).card := by
      gcongr ?a / _
      norm_cast
      apply card_add_mul_card_le_card_add_mul_card_add
    _ ≤ ((B + A).card * (C + C).card) / (A ∩ C).card := by
      gcongr
      apply add_subset_add_left
      apply inter_subset_left
      apply add_subset_add_right
      apply inter_subset_right

lemma triple_add [AddCommGroup α] :
    (A + B + C).card ≤ ((C + A).card * (A+B).card^8 / (A.card^6 * B.card^2) : ℚ) := by
  by_cases hA : A.Nonempty
  by_cases hB : B.Nonempty
  have ⟨u, hu1, hu2⟩ := exists_subset_add_sub A hB
  have ⟨v, hv⟩ := hB.bex
  have int_add : (A + {v}) ∩ (A + B) = (A + {v}) := by
    rw [inter_eq_left]
    apply add_subset_add_left
    simp [hv]
  calc
    ((A + B + C).card : ℚ≥0) = (C + (A + B)).card := by abel_nf
    _ ≤ (C + (A + {v})).card * ((A + B) + (A + B)).card / ((A + {v}) ∩ (A + B)).card := by
      apply add_of_large_intersection
      suffices (A + {v}) ∩ (A + B) = (A + {v}) by simp [this, hA]
      assumption
    _ = (C + A).card * ((A + B) + (A + B)).card / A.card := by
      congr 2
      norm_cast
      rw [←add_assoc]
      simp
      rw [int_add]
      simp
    _ ≤ (C + A).card * (((u + B - B) + B) + ((u + B - B) + B)).card / A.card := by
      gcongr
      apply add_subset_add
      repeat {
        apply add_subset_add
        assumption
        rfl
      }
    _ = (C + A).card * ((u + u) + (4 • B - 2 • B)).card / A.card := by
      congr 4
      repeat rw [sub_eq_add_neg]
      rw [←neg_nsmul]
      generalize -B = C
      abel_nf
    _ ≤ (C + A).card * ((u + u).card * (4 • B - 2 • B).card) / A.card := by
      gcongr
      norm_cast
      apply card_add_le
    _ ≤ (C + A).card * (u.card^2 * (4 • B - 2 • B).card) / A.card := by
      gcongr
      norm_cast
      rw [sq]
      apply card_add_le
    _ ≤ (C + A).card * (((A+B).card / B.card)^2 * (((A+B).card / A.card)^(4+2) * A.card)) / A.card := by
      gcongr
      rw [le_div_iff]
      norm_cast
      norm_cast
      apply Finset.Nonempty.card_pos hB
      apply card_nsmul_sub_nsmul_le
      assumption
    _ = (C + A).card * (A+B).card^8 / (A.card^6 * B.card^2) := by field_simp; ring_nf
  · simp_all
  · simp_all

lemma additive_mul_eq [Field α] (C : α) (h : C ≠ 0) : E[A, C • A] = ((((A ×ˢ A) ×ˢ A ×ˢ A)).filter
    fun x : (α × α) × α × α => x.1.1 + C * x.1.2 = x.2.1 + C * x.2.2).card := calc
  _ = (((A ×ˢ A) ×ˢ (C • A) ×ˢ (C • A)).filter
      fun x : (α × α) × α × α => x.1.1 + x.2.1 = x.1.2 + x.2.2).card := rfl
  _ = ((((A ×ˢ A) ×ˢ A ×ˢ A)).filter
      fun x : (α × α) × α × α => x.1.1 + C • x.2.1 = x.1.2 + C • x.2.2).card := by
    norm_cast
    apply Eq.symm
    apply card_congr (fun ⟨x1, x2⟩ _ => ⟨x1, C • x2⟩)
    · intros a ha
      simp only [smul_eq_mul, filter_congr_decidable, mem_filter, mem_product] at ha
      simp only [mem_filter, mem_product, ha, and_self, Prod.smul_fst, smul_eq_mul,
        Prod.smul_snd, true_and, and_true]
      constructor <;> (apply smul_mem_smul_finset; simp only [ha])
    · intros a c ha hc h
      simp only [Prod.mk.injEq] at h
      cases a
      cases c
      rw [smul_right_inj] at h
      simp at h
      simp [h]
      field_simp
      assumption
    · intros a ha
      exists ⟨a.1, C⁻¹ • a.2⟩
      simp only [inv_div, smul_eq_mul, filter_congr_decidable, mem_filter, mem_product,
        Prod.smul_fst, Prod.smul_snd, exists_prop]
      simp only [mem_filter, mem_product] at ha
      repeat constructor
      · exact ha.1.1.1
      · exact ha.1.1.2
      constructor
      · have := ha.1.2.1
        rw [mem_smul_finset] at this
        have ⟨y, hy, hY⟩ := this
        field_simp at hY
        suffices C⁻¹ * a.2.1 = y by rw [this]; exact hy
        apply Eq.symm
        field_simp
        rw [mul_comm, hY]
      · have := ha.1.2.2
        rw [mem_smul_finset] at this
        have ⟨y, hy, hY⟩ := this
        field_simp at hY
        suffices C⁻¹ * a.2.2 = y by rw [this]; exact hy
        apply Eq.symm
        field_simp
        rw [mul_comm, hY]
      · rw [←mul_assoc]
        field_simp
        rw [ha.2]
        ring
      · rw [←smul_assoc]
        field_simp
  _ = ((((A ×ˢ A) ×ˢ A ×ˢ A)).filter
      fun x : (α × α) × α × α => x.1.1 + C * x.1.2 = x.2.1 + C * x.2.2).card := by
    norm_cast
    apply card_congr (fun ⟨⟨a1, a2⟩, ⟨a3, a4⟩⟩ _ => ⟨⟨a1, a3⟩, ⟨a2, a4⟩⟩)
    · intros a ha
      simp at ha
      simp [ha]
    · intros _ _ _ _ h
      simp at h
      rw [Prod.ext_iff, Prod.ext_iff, Prod.ext_iff]
      simp [h]
    · intros a ha
      exists ((a.1.1, a.2.1), (a.1.2, a.2.2))
      simp at ha
      simp [ha]
