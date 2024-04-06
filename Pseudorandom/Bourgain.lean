import Pseudorandom.Extractor
import Pseudorandom.XorLemma
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Pseudorandom.Incidence.Incidence

open Finset BigOps ComplexConjugate

theorem AddChar.eq_iff [AddGroup α] [GroupWithZero R] (χ : AddChar α R) : χ a = χ b ↔ χ (a - b) = 1 := by
  simp [sub_eq_add_neg, AddChar.map_add_mul, AddChar.map_neg_inv]
  apply Iff.symm
  apply mul_inv_eq_one₀
  apply_fun (· * χ (-b))
  simp only [zero_mul, ne_eq, ← AddChar.map_add_mul, add_right_neg, map_zero_one, one_ne_zero, not_false_eq_true]

def IP [CommSemiring α] : BilinForm α (α × α) := {
  bilin := fun x y => (x.1*y.1 + x.2*y.2)
  bilin_add_left := by intros; simp; ring_nf
  bilin_add_right := by intros; simp; ring_nf
  bilin_smul_left := by intros; simp; ring_nf
  bilin_smul_right := by intros; simp; ring_nf
}

lemma IP_comm [CommSemiring α] (a b : α × α) : IP a b = IP b a := by
  unfold IP
  simp [mul_comm]

theorem apply_inner_product_injective [Field α] (χ : AddChar α ℂ) (h : χ.IsNontrivial) :
    Function.Injective (fun x : α × α => {
      toFun := fun y : α × α => χ (IP x y)
      map_zero_one' := by simp
      map_add_mul' := by
        intro a b
        simp [← AddChar.map_add_mul]
      : AddChar (α × α) ℂ
    }) := by
  obtain ⟨x, hx⟩ := h
  rintro ⟨a1, a2⟩ ⟨b1, b2⟩ v
  simp only [AddChar.mk.injEq] at v
  simp only [Prod.mk.injEq]
  constructor
  · by_contra! nh
    apply sub_ne_zero_of_ne at nh
    have := congr($v (x / (a1 - b1), 0))
    simp only [mul_zero, add_zero] at this
    rw [AddChar.eq_iff] at this
    replace this : χ x = 1 := by
      convert this
      unfold IP
      field_simp
      ring_nf
    simp [this] at hx
  · by_contra! nh
    apply sub_ne_zero_of_ne at nh
    have := congr($v (0, x / (a2 - b2)))
    simp only [mul_zero, add_zero] at this
    rw [AddChar.eq_iff] at this
    replace this : χ x = 1 := by
      convert this
      unfold IP
      field_simp
      ring_nf
    simp [this] at hx

theorem apply_inner_product_bijective [Fintype α] [Field α] (χ : AddChar α ℂ) (h : χ.IsNontrivial) :
    Function.Bijective (fun x : α × α => {
      toFun := fun y : α × α => χ (IP x y)
      map_zero_one' := by simp
      map_add_mul' := by
        intro a b
        simp [← AddChar.map_add_mul]
      : AddChar (α × α) ℂ
    }) := (Fintype.bijective_iff_injective_and_card _).mpr ⟨apply_inner_product_injective χ h, by simp⟩

noncomputable def AddChar.inner_product_equiv [Fintype α] [Field α] (χ : AddChar α ℂ) (h : χ.IsNontrivial) :
  (α × α) ≃ AddChar (α × α) ℂ := Equiv.ofBijective _ (apply_inner_product_bijective χ h)

theorem bourgain_extractor_aux₀ [Fintype α] [Field α] (a b : (α × α) → ℝ) (χ : AddChar α ℂ) (h : χ.IsNontrivial) :
    ‖ ∑ x, a x * ∑ y, b y * χ (IP x y)‖^2 ≤ (Fintype.card α)^2 * ‖a‖_[2]^2 * ‖b‖_[2]^2 :=
      calc ‖ ∑ x, a x * ∑ y, b y * χ (IP x y)‖^2
  _ = ‖ ∑ x, a x * ∑ y, b y * (χ.inner_product_equiv h x) y‖^2 := rfl
  _ = ‖ ∑ x, a x * ∑ y, (χ.inner_product_equiv h x) y * b y‖^2 := by congr; ext; congr; ext; rw [mul_comm]
  _ = ‖ ∑ x, a x * ∑ y, conj ((χ.inner_product_equiv h x)⁻¹ y) * b y‖^2 := by
    congr; ext; congr; ext
    rw [AddChar.inv_apply, AddChar.map_neg_eq_conj, RingHomCompTriple.comp_apply, RingHom.id_apply]
  _ = ‖ ∑ x, a x * (dft (b ·) (χ.inner_product_equiv h x)⁻¹)‖^2 := rfl
  _ = ‖ l2Inner (Complex.ofReal ∘ a) (fun x => dft (b ·) (χ.inner_product_equiv h x)⁻¹)‖^2 := by
    unfold l2Inner
    rcongr
    simp only [Function.comp_apply, Complex.ofReal_eq_coe, Complex.conj_ofReal]
  _ ≤ (‖(Complex.ofReal ∘ a)‖_[2] * ‖(fun x => dft (b ·) (χ.inner_product_equiv h x)⁻¹) ‖_[2])^2 := by
    gcongr
    apply norm_l2Inner_le_lpNorm_mul_lpNorm
    rw [NNReal.isConjExponent_iff_eq_conjExponent]
    rw [NNReal.sub_def]
    norm_num
    norm_num
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * ‖(fun x => dft (b ·) (χ.inner_product_equiv h x)⁻¹) ‖_[2]^2 := by
    ring_nf
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * ∑ x, ‖dft (b ·) (χ.inner_product_equiv h x)⁻¹‖^2 := by
    conv =>
      lhs
      rhs
      rw [l2Norm_sq_eq_sum]
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * ∑ x, ‖dft (b ·) ((AddChar.inner_product_equiv χ h).trans (Equiv.inv _) x)‖^2 := rfl
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * ∑ x, ‖dft (b ·) x‖^2 := by
    congr 1
    apply Fintype.sum_equiv ((AddChar.inner_product_equiv χ h).trans (Equiv.inv _))
    intros
    rfl
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * (Fintype.card (α × α) * 𝔼 x, ‖dft (b ·) x‖^2) := by
    congr 2
    rw [Finset.expect_univ, ← nnratCast_smul_eq_nnqsmul ℝ]
    field_simp
    ring_nf
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * (Fintype.card (α × α) * ‖dft (b ·)‖ₙ_[2]^2) := by
    rw [nl2Norm_sq_eq_expect]
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * (Fintype.card (α × α) * ‖(Complex.ofReal ∘ b)‖_[2]^2) := by
    rw [nl2Norm_dft]
    rfl
  _ = ‖(Complex.ofReal ∘ a)‖_[2]^2 * ((Fintype.card α)^2 * ‖(Complex.ofReal ∘ b)‖_[2]^2) := by
    congr
    simp only [Fintype.card_prod, Nat.cast_mul, sq]
  _ = (Fintype.card α)^2 * ‖(Complex.ofReal ∘ a)‖_[2]^2 * ‖(Complex.ofReal ∘ b)‖_[2]^2 := by ring
  _ = (Fintype.card α)^2 * ‖(Complex.ofReal' ∘ a)‖_[2]^2 * ‖(Complex.ofReal' ∘ b)‖_[2]^2 := rfl
  _ = (Fintype.card α)^2 * ‖a‖_[2]^2 * ‖b‖_[2]^2 := by
    rw [Complex.lpNorm_coe_comp, Complex.lpNorm_coe_comp]

theorem bourgain_extractor_aux₀' [Fintype α] [Field α] (a b : (α × α) → ℝ) (χ : AddChar α ℂ) (h : χ.IsNontrivial) :
    ‖ ∑ x, a x * ∑ y, b y * χ (IP x y)‖ ≤ (Fintype.card α) * ‖a‖_[2] * ‖b‖_[2] := by
  have := bourgain_extractor_aux₀ a b χ h
  rw [← mul_pow, ← mul_pow, sq_le_sq, abs_of_nonneg, abs_of_nonneg] at this
  exact this
  positivity
  positivity

theorem bourgain_extractor_aux₁ [Fintype α] [Field α] [Fintype β] [AddCommGroup β] [Module α β]
    (a b : FinPMF β) (χ : AddChar α ℂ) (F : BilinForm α β) :
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

theorem bourgain_extractor_aux₁' [Fintype α] [Field α] [Fintype β] [AddCommGroup β] [Module α β]
    (a b : FinPMF β) (χ : AddChar α ℂ) (F : BilinForm α β) :
    ‖ ∑ x, a x * ∑ y, b y * χ (F x y)‖ ≤ ‖ ∑ x, a x * ∑ y, (b - b) y * χ (F x y)‖^(2⁻¹ : ℝ) := by
  rw [Real.le_rpow_inv_iff_of_pos, Real.rpow_two]
  apply bourgain_extractor_aux₁ a b χ F
  simp only [Complex.norm_eq_abs, apply_nonneg]
  simp only [Complex.norm_eq_abs, apply_nonneg]
  norm_num


noncomputable def close_high_entropy [Fintype α] (n : ℕ) (ε : ℝ) (a : FinPMF α) : Prop :=
  ∀ (H : Finset α), (H.card ≤ n) → ∑ v ∈ H, a v ≤ ε

theorem bourgain_extractor_aux₂ (ε : ℝ) (hε : 0 < ε) (n : ℕ+) [Fintype α] [Field α] [DecidableEq (α × α)] (a b : FinPMF (α × α)) (χ : AddChar α ℂ)
    (h : χ.IsNontrivial) (hA : close_high_entropy n ε a) (hB : close_high_entropy n ε b):
    ‖ ∑ x, a x * ∑ y, b y * χ (IP x y)‖ ≤ Fintype.card α / n + 2 * ε := calc ‖ ∑ x, a x * ∑ y, b y * χ (IP x y)‖
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y) +
      ∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ := by rw [sum_filter_add_sum_filter_not]
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ +
      ‖∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ := norm_add_le ..
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), ‖a x * ∑ y, b y * χ (IP x y)‖ := by
    gcongr
    apply norm_sum_le
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), ‖a x‖ * ‖∑ y, b y * χ (IP x y)‖ := by
    simp only [one_div, Fintype.sum_prod_type, Complex.norm_eq_abs, not_le, norm_mul,
      Complex.abs_ofReal, Real.norm_eq_abs]
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), ‖a x‖ * ∑ y, ‖b y * χ (IP x y)‖ := by
    gcongr
    apply norm_sum_le
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), ‖a x‖ * ∑ y, ‖b y‖ := by simp only [one_div,
        Fintype.sum_prod_type, Complex.norm_eq_abs, not_le, Real.norm_eq_abs, norm_mul,
        Complex.abs_ofReal, AddChar.norm_apply, mul_one]
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => ¬a x ≤ 1/n), a x := by simp only [one_div,
        Fintype.sum_prod_type, Complex.norm_eq_abs, not_le, Real.norm_eq_abs, ge_iff_le,
        FinPMF.nonneg, abs_of_nonneg, FinPMF.sum_coe, mul_one]
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y, b y * χ (IP x y)‖ + ε := by
    gcongr
    apply hA
    sorry
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x *
      (∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y) + ∑ y ∈ univ.filter (fun y => ¬b y ≤ 1/n), b y * χ (IP x y))‖ + ε := by
    simp_rw [sum_filter_add_sum_filter_not]
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y) +
      ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => ¬b y ≤ 1/n), b y * χ (IP x y)‖ + ε := by
    simp_rw [mul_add, sum_add_distrib]
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ‖∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => ¬b y ≤ 1/n), b y * χ (IP x y)‖ + ε := by
    gcongr
    apply norm_add_le
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), ‖a x * ∑ y ∈ univ.filter (fun y => ¬b y ≤ 1/n), b y * χ (IP x y)‖ + ε := by
    gcongr
    apply norm_sum_le
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), ‖a x‖ * ‖∑ y ∈ univ.filter (fun y => ¬b y ≤ 1/n), b y * χ (IP x y)‖ + ε := by
    simp only [one_div, Complex.norm_eq_abs, not_le, norm_mul, Complex.abs_ofReal, Real.norm_eq_abs]
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), ‖a x‖ * ∑ y ∈ univ.filter (fun y => ¬b y ≤ 1/n), ‖b y * χ (IP x y)‖ + ε := by
    gcongr
    apply norm_sum_le
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => ¬b y ≤ 1/n), b y + ε := by
    simp only [one_div, Complex.norm_eq_abs, Real.norm_eq_abs, ge_iff_le, FinPMF.nonneg,
      abs_of_nonneg, not_le, norm_mul, Complex.abs_ofReal, AddChar.norm_apply, mul_one]
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ε + ε := by
    gcongr
    simp
    apply hB
    sorry
  _ ≤ ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ∑ x ∈ univ, a x * ε + ε := by
    gcongr
    apply sum_le_sum_of_subset_of_nonneg
    simp
    intros
    apply mul_nonneg
    simp
    exact le_of_lt hε
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      ε + ε := by rw [← sum_mul]; simp
  _ = ‖ ∑ x ∈ univ.filter (fun x => a x ≤ 1/n), a x * ∑ y ∈ univ.filter (fun y => b y ≤ 1/n), b y * χ (IP x y)‖ +
      2 * ε := by ring
  _ = ‖ ∑ x, (if a x ≤ 1/n then a x else 0) *
        ∑ y, (if b y ≤ 1/n then b y else 0) * χ (IP x y)‖ +
      2 * ε := by
    congr 2
    apply Finset.sum_subset_zero_on_sdiff
    · simp
    · intros
      simp_all
    · intros
      simp_all only [one_div, mem_filter, mem_univ, true_and, ite_true,
        mul_eq_mul_left_iff, Complex.ofReal_eq_zero]
      left
      apply Finset.sum_subset_zero_on_sdiff
      · simp
      · intros
        simp_all
      · intros
        simp_all
  _ ≤ (Fintype.card α) * ‖fun x => (if a x ≤ 1/n then a x else 0)‖_[2] * ‖fun y => (if b y ≤ 1/n then b y else 0)‖_[2] + 2*ε := by
    gcongr
    apply bourgain_extractor_aux₀'
    exact h
  _ ≤ (Fintype.card α) * Real.sqrt (‖fun x => (if a x ≤ 1/n then a x else 0)‖_[1] * ‖fun x => (if a x ≤ 1/n then a x else 0)‖_[⊤])
      * Real.sqrt (‖fun y => (if b y ≤ 1/n then b y else 0)‖_[1] * ‖fun y => (if b y ≤ 1/n then b y else 0)‖_[⊤]) + 2*ε := by
    gcongr <;> apply l2Norm_le_sqrt_l1Norm_mul_linftyNorm
  _ = (Fintype.card α) * Real.sqrt ((∑ x, ‖if a x ≤ 1/n then a x else 0‖) * ‖fun x => (if a x ≤ 1/n then a x else 0)‖_[⊤])
      * Real.sqrt ((∑ y, ‖if b y ≤ 1/n then b y else 0‖) * ‖fun y => (if b y ≤ 1/n then b y else 0)‖_[⊤]) + 2*ε := by
    rw [l1Norm_eq_sum, l1Norm_eq_sum]
  _ ≤ (Fintype.card α) * Real.sqrt ((∑ x, a x) * (1/n))
      * Real.sqrt ((∑ y, b y) * (1 / n)) + 2*ε := by
    gcongr
    repeat {
    apply Real.sqrt_le_sqrt
    gcongr
    · simp
    · split
      simp [abs_of_nonneg]
      simp
    · rw [linftyNorm_eq_ciSup]
      apply ciSup_le
      intro
      split
      simp_all only [one_div, Real.norm_eq_abs, ge_iff_le, FinPMF.nonneg, abs_of_nonneg]
      simp
    }
  _ = (Fintype.card α) * (Real.sqrt (1/n) * Real.sqrt (1 / n)) + 2*ε := by simp [mul_assoc]
  _ = (Fintype.card α) * (1 / n) + 2*ε := by rw [← sq]; simp
  _ = Fintype.card α / n + 2 * ε := by ring

variable {p : ℕ} [Fact p.Prime]

local notation "α" => ZMod p


noncomputable def lapply (a : FinPMF α) (b : FinPMF (α × α × α)) : FinPMF (α × α) :=
  (a * b).apply (fun ⟨x, y⟩ => (x + y.1, y.2.1 * (x + y.1) + y.2.2))

theorem line_point_large_l2_aux (n : ℕ+) (β : ℝ) (hβ : 0 < β) (hkl : (p^β : ℝ) ≤ n) (hku: n ≤ (p^(2 - β) : ℝ))
    (a' : {x : Finset α // x.Nonempty}) (b' : {x : Finset (α × α × α) // x.Nonempty})
    (hD : Set.InjOn Prod.snd (b' : Set (α × α × α))) (hbSz : b'.1.card ≤ n) :
    close_high_entropy n (1/(a'.1.card * b'.1.card) * ST_C * n^(3/2 - ST_prime_field_eps β)) (lapply (Uniform a') (Uniform b')) := by
  intro H hhSz
  let a := Uniform a'
  let b := Uniform b'
  change ∑ x ∈ H, lapply a b x ≤ _
  calc ∑ x ∈ H, ((a * b).apply (fun ⟨x, y⟩ => (x + y.1, y.2.1 * (x + y.1) + y.2.2))) x
    _ = ∑ z ∈ H,
        ∑ y ∈ (univ.filter (fun ⟨x, y⟩ => (x + y.1, y.2.1 * (x + y.1) + y.2.2) = z) : Finset (α × α × α × α)), a y.1 * b y.2 := by
      unfold FinPMF.apply transfer
      dsimp only [FinPMF.val_apply]
      rcongr
    _ = ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        (if y.1 ∈ a'.1 then 1 / a'.1.card else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 / b'.1.card else 0 : ℝ) := by
      rcongr
      · unfold_let a
        unfold Uniform
        dsimp only [FinPMF.val_apply]
        congr
      · unfold_let b
        unfold Uniform
        dsimp only [FinPMF.val_apply]
        congr
    _ = ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        (1/a'.1.card * (if y.1 ∈ a'.1 then 1 else 0 : ℝ)) * (1/b'.1.card * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)) := by
      simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, mul_one]
    _ = ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        1/(a'.1.card*b'.1.card) * ((if y.1 ∈ a'.1 then 1 else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)) := by
      congr
      ext
      congr
      ext
      ring_nf
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        ((if y.1 ∈ a'.1 then 1 else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)) := by simp only [← mul_sum]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x),
        (if y.1 ∈ a'.1 ∧ y.2 ∈ b'.1 then 1 else 0 : ℝ) := by
      rcongr
      rw [ite_zero_mul_ite_zero]
      simp
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x ∧ z ∈ a'.1 ∧ y ∈ b'.1)).card := by
      simp only [one_div, sum_boole, Nat.cast_sum, add_right_inj, Finset.filter_filter]
    _ ≤ 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (univ.filter (fun (⟨z, y⟩ : α×α×α×α) => (z + y.1, y.2.1 * (z + y.1) + y.2.2) = x ∧ y ∈ b'.1)).card := by
      gcongr
      apply Finset.monotone_filter_right
      rw [Pi.le_def]
      intros
      simp_all only [le_Prop_eq, and_self, and_imp, implies_true]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (univ.filter (fun (y : α × α ) => y.1 * x.1 + y.2 = x.2 ∧ y ∈ b'.1.image Prod.snd)).card := by
      congr
      ext x
      have ⟨x1, x2⟩ := x
      apply Finset.card_congr (fun x _ => x.2.2)
      · intros a ha
        simp_all only [Prod.mk.injEq, mem_filter, mem_univ, true_and, mem_image]
        rw [← ha.1.1]
        exact ⟨ha.1.2, a.2, ha.2, rfl⟩
      · rintro ⟨a1, a2, a3⟩ ⟨b1, b2, b3⟩ ha hb _
        simp only [Prod.mk.injEq, mem_filter, mem_univ, true_and] at ha
        simp only [Prod.mk.injEq, mem_filter, mem_univ, true_and] at hb
        have := hD ha.2 hb.2
        simp_all only [Prod.mk.injEq, and_true, forall_true_left]
        linear_combination ha.1 - hb.1.1
      · intros b hb
        simp only [mem_image, mem_filter, mem_univ, true_and] at hb
        have ⟨hb, a, ha⟩ := hb
        exists ⟨x1 - a.1, a⟩
        simp_all only [Prod.exists, exists_eq_right, true_and, Prod.mk.injEq,
          mem_filter, mem_univ, sub_add_cancel, and_self, exists_const]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ((b'.1.image Prod.snd).filter (fun (y : α × α) => y.1 * x.1 + y.2 = x.2)).card := by
      congr
      ext
      congr 1
      conv =>
        rhs
        rw [← Finset.filter_univ_mem (b'.1.image Prod.snd)]
      rw [Finset.filter_filter]
      simp_rw [and_comm]
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        ((b'.1.image Prod.snd).filter (fun (y : α × α) => x ∈ Line.of_equation y.1 y.2)).card := by
      rcongr
      apply Iff.symm
      apply mem_of_equation_iff
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (((b'.1.image Prod.snd).image (Function.uncurry Line.of_equation)).filter (fun y => x ∈ y)).card := by
      congr
      ext
      apply card_congr (fun x _ => (Function.uncurry Line.of_equation) x)
      · intros x hx
        simp_all only [mem_filter, mem_image, Function.uncurry_apply_pair]
        constructor
        exact ⟨x, hx.1, rfl⟩
        exact hx.2
      · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ _ _ h
        exact Line.uncurry_of_equation_injective h
      · intros b hb
        simp only [mem_filter, mem_image, Function.uncurry_apply_pair] at hb
        have ⟨⟨⟨l1, l2⟩, hl, h⟩, hm⟩ := hb
        exists (l1, l2)
        simp_all
    _ = 1/(a'.1.card*b'.1.card) * ∑ x ∈ H,
        (IntersectionsL x ((b'.1.image Prod.snd).image (Function.uncurry Line.of_equation))).card := rfl
    _ = 1/(a'.1.card*b'.1.card) * (Intersections H ((b'.1.image Prod.snd).image (Function.uncurry Line.of_equation))).card := by rw [IntersectionsL_sum]
    _ ≤ 1/(a'.1.card*b'.1.card) * (ST_C * n^(3/2 - ST_prime_field_eps β)) := by
      gcongr
      apply ST_prime_field
      exact hβ
      exact_mod_cast hkl
      exact_mod_cast hku
      exact hhSz
      exact Finset.card_image_le.trans (Finset.card_image_le.trans hbSz)
    _ = 1/(a'.1.card * b'.1.card) * ST_C * n^(3/2 - ST_prime_field_eps β) := by ring


def lmap (x : α × α) : α × α × α := (x.1 + x.2, (2 * (x.1 + x.2), -((x.1 + x.2)^2 + (x.1^2 + x.2^2))))

def decoder (x : α × α) : α × α := (x.1, x.1^2 - x.2)

lemma jurl (b : FinPMF α) :
    ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) =
    (lapply b ((b * b).apply lmap)).apply decoder := calc
  ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2))
  _ = ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, (x.1.1 + x.1.2 + x.2)^2 - (x.1.1^2 + x.1.2^2 + x.2^2))).apply
      fun x => (x.1, x.1^2 - x.2) := by
    rw [FinPMF.apply_apply]
    congr
    ext x
    rfl
    dsimp
    ring_nf
  _ = ((b * b * b).apply fun x => (x.2 + (x.1.1 + x.1.2), 2 * (x.1.1 + x.1.2) * (x.2 + (x.1.1 + x.1.2)) + -((x.1.1 + x.1.2)^2 + (x.1.1^2 + x.1.2^2)))).apply
      fun x => (x.1, x.1^2 - x.2) := by
    congr
    ext x
    ring
    ring
  _ = (lapply (b.apply id) ((b * b).apply lmap)).apply decoder := by
    congr 1
    unfold lapply
    rw [FinPMF.apply_mul, FinPMF.apply_apply]
    conv =>
      rhs
      arg 1
      rw [← FinPMF.apply_swap]
    rw [FinPMF.apply_apply]
    rfl
  _ = (lapply b ((b * b).apply lmap)).apply decoder := by
    congr
    rw [FinPMF.eq_apply_id]

theorem bourgain_extractor (ε : ℝ) (a b : FinPMF α) (χ : AddChar α ℂ) (h : χ.IsNontrivial) :
    ‖∑ x, a x * ∑ y, b y * χ (x * y + x^2 * y^2)‖ ≤ ε := by
  let a' := a.apply fun x => (x, x^2)
  let b' := b.apply fun x => (x, x^2)
  calc ‖∑ x, a x * ∑ y, b y * χ (x * y + x^2 * y^2)‖
  -- _ = ‖∑ x, a x * ∑ y, (b.apply fun x => (x, x^2)) y * χ (x * y.1 + x^2 * y.2)‖ := by
  --   congr with _
  --   congr 1
  --   apply Eq.symm
  --   apply apply_weighted_sum
  -- _ = ‖∑ x, (a.apply fun x => (x, x^2)) x * ∑ y, (b.apply fun x => (x, x^2)) y * χ (x.1 * y.1 + x.2 * y.2)‖ := by
  --   congr 1
  --   apply Eq.symm
  --   apply apply_weighted_sum
  -- _ = ‖∑ x, a' x * ∑ y, b' y * χ (IP x y)‖ := rfl
  -- _ ≤ ‖∑ x, a' x * ∑ y, (b' - b') y * χ (IP x y)‖^(2⁻¹ : ℝ) := bourgain_extractor_aux₁' ..
  -- _ ≤ (‖∑ x, a' x * ∑ y, ((b' - b') - (b' - b')) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ ≤ ((‖∑ x, a' x * ∑ y, (((b' - b') - (b' - b')) - ((b' - b') - (b' - b'))) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
    -- gcongr
    -- apply bourgain_extractor_aux₁'
  -- _ = ((‖∑ x, a' x * ∑ y, ((b' + b' + b') + (b' - b' - b' - b' - b')) y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
    -- rcongr
    -- simp only [FinPMF.sub_eq_add_neg, FinPMF.neg_add, FinPMF.neg_neg]
    -- generalize -b'=c'
    -- abel
  -- _ ≤ ((‖∑ x, a' x * ∑ y, (b' + b' + b') y * χ (IP x y)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ) := by
  --   gcongr
  --   sorry
  -- _ = ‖∑ x, a' x * ∑ y, (b' + b' + b') y * χ (IP x y)‖^(8⁻¹ : ℝ) := by
  --   rw [← Real.rpow_mul, ← Real.rpow_mul]
  --   congr
  --   norm_num
  --   positivity
  --   positivity
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, a' x * χ (IP x y)‖^(8⁻¹ : ℝ) := by
  --   simp_rw [mul_sum]
  --   rw [sum_comm]
  --   congr with _
  --   congr with _
  --   ring
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, a' x * χ (IP y x)‖^(8⁻¹ : ℝ) := by
  --   simp_rw [IP_comm]
  -- _ ≤ (‖∑ y, (b' + b' + b') y * ∑ x, (a' - a') x * χ (IP y x)‖^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ ≤ ((‖∑ y, (b' + b' + b') y * ∑ x, ((a' - a') - (a' - a')) x * χ (IP y x)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ ≤ (((‖∑ y, (b' + b' + b') y * ∑ x, (((a' - a') - (a' - a')) - ((a' - a') - (a' - a'))) x * χ (IP y x)‖^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(2⁻¹ : ℝ))^(8⁻¹ : ℝ) := by
  --   gcongr
  --   apply bourgain_extractor_aux₁'
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, (((a' - a') - (a' - a')) - ((a' - a') - (a' - a'))) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
  --   rw [← Real.rpow_mul, ← Real.rpow_mul, ← Real.rpow_mul]
  --   congr
  --   norm_num
  --   repeat positivity
  -- _ = ‖∑ y, (b' + b' + b') y * ∑ x, ((a' + a' + a') + (a' - a' - a' - a' - a')) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
  --   rcongr
  --   simp only [FinPMF.sub_eq_add_neg, FinPMF.neg_add, FinPMF.neg_neg]
  --   generalize -a'=c'
  --   abel
  _ ≤ ‖∑ y, (b' + b' + b') y * ∑ x, (a' + a' + a') x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
    -- gcongr
    sorry
  _ = ‖∑ y, ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) y *
      ∑ x, ((a * a * a).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
    rcongr
    · unfold_let b'
      rw [FinPMF.apply_add, FinPMF.apply_add]
      rfl
    · unfold_let a'
      rw [FinPMF.apply_add, FinPMF.apply_add]
      rfl
  _ = ‖∑ y, ((lapply b ((b * b).apply lmap)).apply decoder) y *
      ∑ x, ((lapply a ((a * a).apply lmap)).apply decoder) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
    simp_rw [jurl]
  -- _ = ‖∑ y, ((b * b * b).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) y *
  --     ∑ x, ((a * a * a).apply fun x => (x.1.1 + x.1.2 + x.2, x.1.1^2 + x.1.2^2 + x.2^2)) x * χ (IP y x)‖^(64⁻¹ : ℝ) := by
  _ ≤ ε := by

    sorry
  _ = ε := rfl
