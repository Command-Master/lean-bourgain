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

open NNRat Classical Real BigOps Finset Pointwise

variable {α : Type*} [Field α] [Fintype α]
  (A B C : Finset α)

lemma sub_le_add : (A - B).card ≤ ((A + B).card^3 / (A.card * B.card) : ℚ≥0) := by
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

lemma card_of_inv (a : α) (h : a ≠ 0) : (a • A).card = A.card := by
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

lemma add_le_of_add_add (h : B.Nonempty) : (A+C).card ≤ ((A + B).card * (B+C).card^3 / (B.card^2 * C.card) : ℚ≥0) := by
  calc ((A+C).card : ℚ≥0)
    _ = (A+C).card * B.card / B.card := by field_simp
    _ ≤ ((A + B).card * (B - C).card) / B.card := by gcongr ?a / _; norm_cast; apply card_add_mul_le_card_add_mul_card_sub
    _ ≤ (A + B).card * ((B + C).card^3 / (B.card * C.card)) / B.card := by
      gcongr
      apply sub_le_add
    _ = (A + B).card * (B+C).card^3 / (B.card^2 * C.card) := by field_simp; ring_nf

lemma add_of_large_intersection (h : (A ∩ C).Nonempty) : (B+C).card ≤ ((B + A).card * (C+C).card / (A ∩ C).card : ℚ≥0) := by
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

lemma triple_add :
    (A + B + C).card ≤ ((C + A).card * (A+B).card^8 / (A.card^6 * B.card^2) : ℚ≥0) := by
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
