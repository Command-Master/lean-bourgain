import Pseudorandom.Extractor
import Mathlib.LinearAlgebra.BilinearForm.Basic
import Pseudorandom.Incidence.Incidence

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

-- theorem bourgain_extractor_aux₁ (a b : FinPMF β) (χ : AddChar α ℂ) (F : BilinForm α β) :
--   ‖ ∑ x, a x * ∑ y, b y * χ (F x y)‖^2 ≤ ‖ ∑ x, a x * ∑ y, (b - b) y * χ (F x y)‖ := by

variable {p : ℕ} [Fact p.Prime]

local notation "α" => ZMod p

noncomputable def line_growth (a : FinPMF α) (b : FinPMF (α × α)) : ℝ :=
  ‖(a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2))‖_[2]^2

theorem line_point_large_l2 (k : ℕ+) (β : ℝ) (hβ : 0 < β) (hkl : (p^β : ℝ) ≤ k^2) (hku: k^2 ≤ (p^(2 - β) : ℝ))
    (a' : {x : Finset α // x.card = k}) (b' : {x : Finset (α × α) // x.card = k^2}):
  line_growth (Uniform ⟨a'.1, by
    apply Finset.card_pos.mp
    rw [a'.2]
    apply PNat.pos
    ⟩) (Uniform ⟨b'.1, by
    apply Finset.card_pos.mp
    rw [b'.2]
    simp
    ⟩) ≤ 1/k^2 + ST_C^2 * k^(-4 * ST_prime_field_eps β) := by
  let a := Uniform ⟨a'.1, by
    apply Finset.card_pos.mp
    rw [a'.2]
    apply PNat.pos
    ⟩
  let b := Uniform ⟨b'.1, by
    apply Finset.card_pos.mp
    rw [b'.2]
    simp
    ⟩
  let H := univ.filter fun x => ¬((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x ≤ 1/k^2)
  have hsmall : H.card ≤ k^2 := by
    rify
    calc
      (H.card : ℝ) = (H.card * (1/k^2)) * k^2 := by field_simp
      _ = (∑ x ∈ H, (1 / k^2 : ℝ)) * k^2 := by simp
      _ ≤ (∑ x ∈ H, ((a*b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x : ℝ)) * k^2 := by
        gcongr with i hi
        unfold_let H at hi
        simp at hi
        simp [hi, le_of_lt]
      _ ≤ (∑ x, ((a*b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x : ℝ)) * k^2 := by
        gcongr
        apply Finset.sum_le_sum_of_subset_of_nonneg
        simp
        intros
        simp
      _ = k^2 := by simp
  calc ‖(a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2))‖_[2]^2
    _ = ∑ x, ‖((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x)‖^2 := by
      apply lpNorm_pow_eq_sum
      norm_num
    _ = ∑ x, (((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x))^2 := by
      rcongr
      simp
    _ = ∑ x ∈ univ.filter fun x => ((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x ≤ 1/k^2),
        (((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x))^2
        + ∑ x ∈ univ.filter fun x => ¬((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x ≤ 1/k^2),
        (((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x))^2 := by
      rw [Finset.sum_filter_add_sum_filter_not]
    _ ≤ ∑ x ∈ univ.filter fun x => ((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x ≤ 1/k^2),
        (((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x) * (1/k^2))
        + (∑ x ∈ univ.filter fun x => ¬((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x ≤ 1/k^2),
        ((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x))^2 := by
      gcongr
      · rw [sq]
        gcongr
        simp
        simp_all
      sorry
    _ ≤ ∑ x ∈ univ,
        (((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x) * (1/k^2)) +
        (∑ x ∈ univ.filter fun x => ¬((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x ≤ 1/k^2),
        ((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x))^2 := by
      gcongr
      apply Finset.sum_le_sum_of_subset_of_nonneg
      simp
      intros
      simp
    _ = 1/k^2 + (∑ x ∈ H,
        ((a * b).apply (fun x => (x.1, x.2.1 * x.1 + x.2.2)) x))^2 := by
      rw [← sum_mul, FinPMF.sum_coe, one_mul]
    _ = 1/k^2 + (∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x), a y.1 * b y.2)^2 := by
      unfold FinPMF.apply transfer
      dsimp only [instFunLike]
      rcongr
    _ = 1/k^2 + (∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x),
        (if y.1 ∈ a'.1 then 1 / a'.1.card else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 / b'.1.card else 0 : ℝ))^2 := by
      rcongr
      · unfold_let a
        unfold Uniform
        dsimp only [instFunLike]
        congr
      · unfold_let b
        unfold Uniform
        dsimp only [instFunLike]
        congr
    _ = 1/k^2 + (∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x),
        (if y.1 ∈ a'.1 then 1 / k else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 / k^2 else 0 : ℝ))^2 := by
      rw [a'.2, b'.2]
      norm_cast
    _ = 1/k^2 + (∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x),
        (1/k * (if y.1 ∈ a'.1 then 1 else 0 : ℝ)) * (1/k^2 * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)))^2 := by
      simp only [one_div, mul_ite, ite_mul, zero_mul, mul_zero, mul_one]
    _ = 1/k^2 + (∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x),
        1/k^3 * ((if y.1 ∈ a'.1 then 1 else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)))^2 := by
      congr
      ext
      congr
      ext
      ring_nf
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x),
        ((if y.1 ∈ a'.1 then 1 else 0 : ℝ) * (if y.2 ∈ b'.1 then 1 else 0 : ℝ)))^2 := by simp only [← mul_sum]
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        ∑ y ∈ univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x),
        (if y.1 ∈ a'.1 ∧ y.2 ∈ b'.1 then 1 else 0 : ℝ))^2 := by
      rcongr
      rw [ite_zero_mul_ite_zero]
      simp
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        (univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x ∧ y.1 ∈ a'.1 ∧ y.2 ∈ b'.1)).card)^2 := by
      simp only [one_div, sum_boole, Nat.cast_sum, add_right_inj, Finset.filter_filter]
    _ ≤ 1/k^2 + (1/k^3 * ∑ x ∈ H,
        (univ.filter (fun (y : α × α × α) => (y.1, y.2.1 * y.1 + y.2.2) = x ∧ y.2 ∈ b'.1)).card)^2 := by
      gcongr
      apply Finset.monotone_filter_right
      rw [Pi.le_def]
      intros
      simp_all only [le_Prop_eq, and_self, and_imp, implies_true]
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        (univ.filter (fun (y : α × α) => y.1 * x.1 + y.2 = x.2 ∧ y ∈ b'.1)).card)^2 := by
      congr
      ext x
      have ⟨x1, x2⟩ := x
      apply Finset.card_congr (fun x _ => x.2)
      · intros a ha
        simp_all only [Prod.mk.injEq, mem_filter, mem_univ, true_and, filter_congr_decidable,
          and_true]
        rw [← ha.1.1]
        exact ha.1.2
      · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ _ _ _
        simp_all only [Prod.mk.injEq, mem_filter, mem_univ, true_and]
      · intros b hb
        exists ⟨x1, b⟩
        simp_all only [filter_congr_decidable, mem_filter, mem_univ, true_and, Prod.mk.injEq,
          and_self, exists_const]
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        (b'.1.filter (fun (y : α × α) => y.1 * x.1 + y.2 = x.2)).card)^2 := by
      congr
      ext
      congr 1
      conv =>
        rhs
        rw [← Finset.filter_univ_mem b'.1]
      rw [Finset.filter_filter]
      simp_rw [and_comm]
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        (b'.1.filter (fun (y : α × α) => x ∈ Line.of_equation y.1 y.2)).card)^2 := by
      rcongr
      apply Iff.symm
      apply mem_of_equation_iff
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        ((b'.1.image (Function.uncurry Line.of_equation)).filter (fun y => x ∈ y)).card)^2 := by
      congr
      ext
      apply card_congr (fun x _ => (Function.uncurry Line.of_equation) x)
      · intros x hx
        simp_all only [mem_filter, mem_image, Function.uncurry_apply_pair]
        constructor
        exact ⟨x, hx.1, rfl⟩
        exact hx.2
      · rintro ⟨a1, a2⟩ ⟨b1, b2⟩ ha hb h
        exact Line.uncurry_of_equation_injective h
      · intros b hb
        simp only [mem_filter, mem_image, Function.uncurry_apply_pair] at hb
        have ⟨⟨⟨l1, l2⟩, hl, h⟩, hm⟩ := hb
        exists (l1, l2)
        simp_all
    _ = 1/k^2 + (1/k^3 * ∑ x ∈ H,
        (IntersectionsL x (b'.1.image (Function.uncurry Line.of_equation))).card)^2 := rfl
    _ = 1/k^2 + (1/k^3 * (Intersections H (b'.1.image (Function.uncurry Line.of_equation))).card)^2 := by rw [IntersectionsL_sum]
    _ ≤ 1/k^2 + (1/k^3 * (ST_C * (k^2 : ℕ+)^(3/2 - ST_prime_field_eps β)))^2 := by
      gcongr
      apply ST_prime_field
      exact hβ
      exact_mod_cast hkl
      exact_mod_cast hku
      exact hsmall
      refine Finset.card_image_le.trans ?_
      rw [b'.2]
      rfl
    _ = 1/k^2 + (1/k^3 * (ST_C * k^(2 * (3/2 - ST_prime_field_eps β))))^2 := by
      push_cast
      rw [← Real.rpow_natCast_mul]
      norm_cast
      simp
    _ = 1/k^2 + (ST_C * (k^(3 - 2 * ST_prime_field_eps β) / k^3))^2 := by
      ring_nf
    _ = 1/k^2 + (ST_C * k^(-2 * ST_prime_field_eps β))^2 := by
      rw [← Real.rpow_sub_nat]
      ring_nf
      apply ne_of_gt
      simp
    _ = 1/k^2 + ST_C^2 * k^(-4 * ST_prime_field_eps β) := by
      rw [mul_pow, ← Real.rpow_mul_natCast]
      ring_nf
      simp
