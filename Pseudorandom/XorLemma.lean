import Pseudorandom.SD
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Prereqs.Discrete.DFT.Basic
import LeanAPAP.Prereqs.Expect.Basic

open Classical Real Finset BigOps

variable
   {α : Type u1} [Nonempty α] [Fintype α] [AddCommGroup α]
   (a b : FinPMF α)

open scoped NNReal

-- Note: their DFT isn't normalized.

theorem XOR_lemma' (ε : ℝ≥0) (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖dft (a ·) χ‖ ≤ ε) :
  ∑ x : α, (a x - (Fintype.card α : ℝ)⁻¹)^2 ≤ (ε : ℝ)^2 := by
  let f := (fun x => (a x : ℂ)) - Function.const α ((Fintype.card α : ℂ)⁻¹)
  calc ∑ x : α, (a x - (Fintype.card α : ℝ)⁻¹)^2
    _ = ‖f‖_[2]^2 := by
      simp [lpNorm_eq_sum']
      rw [←rpow_mul_natCast]
      simp
      apply sum_congr
      rfl
      intros
      rw [←(Complex.abs_re_eq_abs).mpr]
      simp [f]
      simp [f]
      apply sum_nonneg
      aesop
    _ = ‖dft f‖ₙ_[2]^2 := by rw [nl2Norm_dft]
    _ = 𝔼 x, ‖dft f x‖^2 := by
      simp [nlpNorm_eq_expect']
      rw [←rpow_mul_natCast]
      simp
      apply expect_nonneg
      aesop
    _ ≤ 𝔼 (x : AddChar α ℂ), (ε : ℝ)^2 := by
      apply expect_le_expect
      intro i _
      rw [sq_le_sq]
      rw [Complex.norm_eq_abs, Complex.abs_abs, NNReal.abs_eq, ←Complex.norm_eq_abs]
      by_cases h₂ : i = 0
      simp [h₂, dft_apply, l2Inner_eq_sum, f]
      have : ∑ x, (a x : ℂ) = Complex.ofReal (∑ x, a x) := by
        simp only [map_sum, Complex.ofReal_eq_coe]
      rw [this]
      simp [card_univ]
      simp [dft_sub, f]
      rw [dft_const]
      simp
      apply h i
      rw [AddChar.isNontrivial_iff_ne_trivial]
      aesop
      aesop
    _ = (ε : ℝ)^2 := by simp

theorem XOR_lemma (ε : ℝ≥0) (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖dft (a ·) χ‖ ≤ ε) :
  SD a (Uniform ⟨univ, univ_nonempty⟩) ≤ 2⁻¹ * ε * Real.sqrt (Fintype.card α) := by
  simp [SD, Uniform.univ_uniform]
  calc ∑ x : α, |2⁻¹ * (a x - (↑(Fintype.card α))⁻¹)|
    _ = Real.sqrt ((∑ x : α, |2⁻¹ * (a x - (↑(Fintype.card α))⁻¹)|)^2) := by
      apply Eq.symm
      apply sqrt_sq
      apply sum_nonneg
      intros
      apply abs_nonneg
    _ ≤ Real.sqrt ((Fintype.card α) * (∑ x : α, |2⁻¹ * (a x - (↑(Fintype.card α))⁻¹)|^2)) := by
      apply Real.sqrt_le_sqrt
      apply sq_sum_le_card_mul_sum_sq
    _ = Real.sqrt ((Fintype.card α) * (∑ x : α, (2⁻¹ * (a x - (↑(Fintype.card α))⁻¹))^2)) := by congr; ext; apply sq_abs
    _ = Real.sqrt ((Fintype.card α) * (∑ x : α, 2⁻¹^2 * (a x - (↑(Fintype.card α))⁻¹)^2)) := by
      congr
      ext
      rw [mul_pow]
    _ = Real.sqrt ((Fintype.card α) * 2⁻¹^2 * (∑ x : α, (a x - (↑(Fintype.card α))⁻¹)^2)) := by
      congr 1
      simp [←mul_sum]
      ring
    _ ≤ Real.sqrt ((Fintype.card α) * 2⁻¹^2 * ε^2) := by
      apply Real.sqrt_le_sqrt
      apply mul_le_mul_of_nonneg_left (XOR_lemma' a ε h)
      simp
    _ = 2⁻¹ * ε * Real.sqrt (Fintype.card α) := by
      rw [Real.sqrt_eq_iff_sq_eq]
      ring_nf
      simp
      apply mul_nonneg
      simp
      apply sq_nonneg
      apply mul_nonneg
      apply mul_nonneg
      simp
      simp
      apply sqrt_nonneg
