import LeanAPAP.Prereqs.Discrete.LpNorm.Compact

variable
   {α : Type*} [αnonempty: Nonempty α] [Fintype α] [AddCommGroup α]
   {β : Type*} [Nonempty β] [Fintype β] [AddCommGroup β]
   [RCLike 𝕜]
   (a b : α → 𝕜)

open Real Finset

open scoped NNReal BigOps

theorem l1Norm_le_sqrt_card_mul_l2Norm :
  ‖a‖_[1] ≤ Real.sqrt (Fintype.card α) * ‖a‖_[2] := calc
    ‖a‖_[1] = ‖1 * a‖_[1] := by simp
    _ ≤ ‖1‖_[(2 : NNReal)] * ‖a‖_[2] := by
      apply l1Norm_mul_le
      rw [NNReal.isConjExponent_iff_eq_conjExponent]
      rw [NNReal.sub_def]
      norm_num
      norm_num
    _ = Real.sqrt (Fintype.card α) * ‖a‖_[2] := by
      congr
      rw [lpNorm_one (p := 2), Real.sqrt_eq_rpow]
      norm_num
      norm_num

lemma lpNorm_eq_card_rpow_mul_nlpNorm (p : NNReal) (hp : p ≠ 0) :
    ‖a‖_[p] = (Fintype.card α)^(p.toReal⁻¹) * ‖a‖ₙ_[p] := calc
  ‖a‖_[p] = (∑ i, ‖a i‖ ^ (p.toReal)) ^ (p.toReal⁻¹) := lpNorm_eq_sum hp ..
  _ = (Fintype.card α * 𝔼 i, ‖a i‖ ^ (p.toReal)) ^ (p.toReal⁻¹) := by
    simp only [Fintype.card_mul_expect]
  _ = (Fintype.card α)^(p.toReal⁻¹) * (𝔼 i, ‖a i‖ ^ (p.toReal)) ^ (p.toReal⁻¹) := by
    rw [mul_rpow]
    simp
    apply expect_nonneg
    intros
    apply rpow_nonneg
    simp
  _ = (Fintype.card α)^(p.toReal⁻¹) * ‖a‖ₙ_[p] := by
    rw [nlpNorm_eq_expect hp]

lemma lpNorm_le_card_rpow_mul_linftyNorm (p : NNReal) (hp : p ≠ 0) :
    ‖a‖_[p] ≤ (Fintype.card α)^(p.toReal⁻¹) * ‖a‖_[⊤] := calc
  ‖a‖_[p] = (∑ i, ‖a i‖ ^ (p.toReal)) ^ (p.toReal⁻¹) := lpNorm_eq_sum hp ..
  _ ≤ (∑ __, ‖a‖_[⊤] ^ (p.toReal)) ^ (p.toReal⁻¹) := by
    gcongr with i
    rw [linftyNorm_eq_ciSup]
    apply le_ciSup (c := i)
    simp [Set.Finite.bddAbove, Set.finite_range]
  _ = (Fintype.card α * ‖a‖_[⊤] ^ (p.toReal)) ^ (p.toReal⁻¹) := by
    simp; rfl
  _ ≤ (Fintype.card α)^(p.toReal⁻¹) * (‖a‖_[⊤] ^ (p.toReal)) ^ (p.toReal⁻¹) := by
    rw [mul_rpow]
    simp
    apply rpow_nonneg
    simp
  _ = (Fintype.card α)^(p.toReal⁻¹) * ‖a‖_[⊤] := by
    congr
    rw [← rpow_mul]
    field_simp
    simp

lemma l2Inner_le_l1Norm_mul_linftyNorm :
    ‖⟪a, b⟫_[𝕜]‖ ≤ ‖a‖_[1] * ‖b‖_[⊤] := by
  rw [l2Inner, l1Norm_eq_sum, sum_mul]
  refine (norm_sum_le ..).trans ?_
  apply sum_le_sum
  intro i _
  simp only [norm_mul, RingHomIsometric.is_iso]
  gcongr
  rw [linftyNorm_eq_ciSup]
  apply le_ciSup (c := i)
  simp [Set.Finite.bddAbove, Set.finite_range]

lemma l2Norm_le_sqrt_l1Norm_mul_linftyNorm (a : α → ℝ) :
    ‖a‖_[2] ≤ Real.sqrt (‖a‖_[1] * ‖a‖_[⊤]) := by
  rw [Real.le_sqrt]
  convert_to ⟪a, a⟫_[ℝ] ≤ ‖a‖_[1] * ‖a‖_[⊤]
  simp
  convert l2Inner_le_l1Norm_mul_linftyNorm a a
  simp
  simp
  apply mul_nonneg <;> simp
