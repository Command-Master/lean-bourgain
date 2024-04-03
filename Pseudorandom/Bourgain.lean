import Pseudorandom.Extractor
import Mathlib.LinearAlgebra.BilinearForm.Basic

open Finset BigOps ComplexConjugate

variable (α : Type*) [Fintype α] [CommRing α] [Fintype β] [AddCommGroup β] [Module α β]

-- set_option pp.analyze true

theorem bourgain_extractor_aux₁ (a b : FinPMF β) (χ : AddChar α ℂ) (F : BilinForm α β) :
    ‖ ∑ x, a x * ∑ y, b y * χ (F x y)‖^2 ≤ ‖ ∑ x, a x * ∑ y, (b - b) y * χ (F x y)‖ := by
  calc ‖ ∑ x, a x * ∑ y, b y * χ (F x y)‖^2
    _ ≤ (∑ x, ‖a x * ∑ y, b y * χ (F x y)‖)^2 := by
      gcongr
      apply norm_sum_le
    _ = (∑ x, a x * ‖∑ y, b y * χ (F x y)‖)^2 := by
      rcongr
      simp
    _ = (∑ x, Real.sqrt (a x) * (Real.sqrt (a x) * ‖∑ y, b y * χ (F x y)‖))^2 := by
      simp_rw [← mul_assoc]
      rcongr
      simp
    _ ≤ (∑ x, Real.sqrt (a x)^2) * (∑ x, (Real.sqrt (a x) * ‖∑ y, b y * χ (F x y)‖)^2) := by
      apply sum_mul_sq_le_sq_mul_sq
    _ = (∑ x, a x) * (∑ x, a x * ‖∑ y, b y * χ (F x y)‖^2) := by
      rcongr
      simp
      ring_nf
      simp only [FinPMF.nonneg, Real.sq_sqrt]
      ring
    _ = ∑ x, a x * ‖∑ y, b y * χ (F x y)‖^2 := by simp
    _ = ‖(∑ x, a x * ‖∑ y, b y * χ (F x y)‖^2 : ℂ)‖ := by
      apply_fun Complex.ofReal'
      push_cast
      apply Complex.eq_coe_norm_of_nonneg
      rw [Complex.nonneg_iff]
      constructor
      simp only [Complex.norm_eq_abs, Complex.re_sum, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero]
      apply sum_nonneg
      intros
      norm_cast
      apply mul_nonneg
      simp
      simp
      simp only [Complex.norm_eq_abs, Complex.im_sum, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, add_zero]
      apply Eq.symm
      apply sum_eq_zero
      intros
      norm_cast
      simp
      exact Complex.ofReal_injective
    _ = ‖(∑ x, a x * Complex.normSq (∑ y, b y * χ (F x y)) : ℂ)‖ := by simp_rw [Complex.normSq_eq_norm_sq]; norm_cast
    _ = ‖(∑ x, a x * (conj (∑ y, b y * χ (F x y)) * ∑ y, b y * χ (F x y)) : ℂ)‖ := by simp_rw [Complex.normSq_eq_conj_mul_self]
    _ = ‖(∑ x, a x * ((∑ y, b y * χ (- F x y)) * ∑ y, b y * χ (F x y)) : ℂ)‖ := by
      rcongr
      simp
      rcongr
      apply Complex.conj_ofReal
      rw [AddChar.map_neg_eq_conj]
    _ = ‖(∑ x, a x * (∑ y₁, ∑ y₂, b y₁ * b y₂ * χ (F x (y₁ - y₂))) : ℂ)‖ := by
      rcongr x
      rw [mul_comm, sum_mul_sum]
      congr with y₁
      congr with y₂
      convert_to ((b y₁) * (b y₂)) * (χ (F x y₁) * χ (- F x y₂)) = ((b y₁) * (b y₂)) * χ (F x (y₁ - y₂))
      ring_nf
      rw [← AddChar.map_add_mul]
      congr
      simp_rw [BilinForm.sub_right (B₁ := F) x y₁ y₂]
      ring_nf
    _ = ‖(∑ x, a x * (∑ y in univ ×ˢ univ, b y.1 * b y.2 * χ (F x (y.1 - y.2))) : ℂ)‖ := by
      congr with x
      congr 1
      rw [Finset.sum_product' (f := fun y₁ y₂ => b y₁ * b y₂ * χ (F x (y₁ - y₂)))]
    _ = ‖(∑ x, a x * (∑ y : β × β, b y.1 * b y.2 * χ (F x (y.1 - y.2))) : ℂ)‖ := rfl
    _ = ‖ ∑ x, a x * ∑ y, (b - b) y * χ (F x y)‖ := by
      congr with x
      congr 1
      simp_rw [instSubFinPMF]
      conv =>
        rhs
        exact apply_weighted_sum ..
      rcongr ⟨x1, x2⟩
      simp
      rfl

variable (p : ℕ) [Fact p.Prime]

local notation "α" => ZMod p
