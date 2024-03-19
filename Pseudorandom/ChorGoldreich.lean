import Pseudorandom.Extractor
import Mathlib.Data.ZMod.Defs

open Classical Finset BigOperators Matrix Real

-- An alternative expression for the statistical distance from uniformity in ℤ₂
lemma SD_Uni2 (a : FinPMF (ZMod 2)) : SD a (Uniform ⟨univ, univ_nonempty⟩) = |∑ x, (a x) * (-1)^(x.val)| * (1/2) := by
  simp [SD]
  conv =>
    lhs
    apply Fin.sum_univ_two
  conv =>
    rhs
    lhs
    rhs
    apply Fin.sum_univ_two
  simp [ZMod.val]
  have : a 0 = 1 - a 1 := by
    apply eq_sub_of_add_eq
    rw [(Fin.sum_univ_two a).symm]
    apply FinPMF.sum_coe
  rw [this]
  ring_nf
  have : -(1/4 + a 1 * (-1/2)) = (-1/4 + a 1 * (1/2)) := by ring
  rw [←this, abs_neg, ←mul_two, mul_one_div]
  field_simp
  rw [mul_assoc, ←abs_of_nonneg (a := (2*2 : ℝ)), ←abs_mul]
  ring_nf
  exact mul_self_nonneg 2

/- For a nontrivial character, the sum over the domain is 0.
   This is only the proof for ℤ₂ⁿ.
-/
lemma inner_product_sum (n : ℕ)
  (x : Fin n → ZMod 2) (h : x ≠ 0) :
  ∑ y : Fin n → ZMod 2, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) = 0 := by
  have : ¬∀ i, x i = 0 := by
    intro v
    suffices x = 0 by trivial
    funext a
    exact v a
  simp at this
  have ⟨i, hi_⟩ := this
  clear this
  have hi : x i = 1 := by
    have := Fin.exists_fin_two.mp (Exists.intro (x i) rfl)
    simp_all
  clear hi_ h
  calc ∑ y : Fin n → ZMod 2, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x)
    _ = ∑ y in univ.filter (fun (x: Fin n → ZMod 2) => x i = 0), (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) +
        ∑ y in (univ.filter (fun (x: Fin n → ZMod 2) => x i = 0))ᶜ, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) := by
      rw [sum_add_sum_compl]
    _ = ∑ y in univ.filter (fun (x: Fin n → ZMod 2) => x i = 0), (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) +
        ∑ y in univ.filter (fun (x: Fin n → ZMod 2) => x i = 0), -(-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) := by
        congr 1
        apply sum_nbij' (fun x => Function.update x i 0) (fun x => Function.update x i 1)
        · intros
          simp
        · intros
          simp
        repeat {
          intros x h
          funext j
          by_cases h₂ : i = j
          · rw [h₂]
            simp
            rw [h₂] at h
            simp at h
            have := Fin.exists_fin_two.mp (Exists.intro (x j) rfl)
            simp_all only [false_or]
          · simp_all
            rw [Function.update_noteq]
            tauto
          }
        · intros y h'
          simp_all
          have h : y i = 1 := by
            have := Fin.exists_fin_two.mp (Exists.intro (y i) rfl)
            simp_all
          clear h'
          rw [neg_eq_neg_one_mul ((-1) ^ _), ←pow_succ]
          rw [(_ : 1 = ZMod.val (1 : ZMod 2))]
          conv =>
            rhs
            rw [neg_one_pow_eq_pow_mod_two, ←ZMod.val_add]
          congr
          simp [Matrix.dotProduct]
          conv =>
            congr <;> rw [sum_eq_add_sum_diff_singleton (i := i) (mem_univ i)]
          simp only [h, hi, mul_one, Function.update_same, zero_add, add_comm]
          congr 1
          apply sum_congr
          rfl
          aesop
          trivial
    _ = 0 := by simp

/- Any two different characters are orthogonal.
   This is only the proof for ℤ₂ⁿ.
-/
lemma inner_product_orthogonal (n : ℕ)
  (x z : Fin n → ZMod 2) (h : x ≠ z) :
  ∑ y : Fin n → ZMod 2, (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ x) * (-1 : ℝ) ^ ZMod.val (y ⬝ᵥ z) = 0 := by
  simp [←pow_add]
  conv =>
    lhs
    rhs
    intro x
    rw [neg_one_pow_eq_pow_mod_two, ←ZMod.val_add, ←dotProduct_add]
  apply inner_product_sum
  intro v
  suffices x = z by contradiction
  funext i
  apply sub_eq_zero.1
  have : (x + z) i = (0 : Fin n → ZMod 2) i := by rw [v]
  simp_all

-- The Chor-Goldreich Extractor
theorem inner_product_extractor (n k : ℕ) : two_extractor (fun (x : (Fin n → ZMod 2) × (Fin n → ZMod 2)) => Matrix.dotProduct x.1 x.2)
  k (2^(n/2 - k - 1 : ℝ)) := by
  simp only [two_extractor, ge_iff_le, and_imp]
  intros a b _ _
  rw [SD_Uni2]
  simp [apply_weighted_sum]
  calc |∑ x : Fin n → ZMod 2, ∑ x_1 : Fin n → ZMod 2, a x * b x_1 * (-1) ^ ZMod.val (x ⬝ᵥ x_1)| * 2⁻¹
    _ = |a ⬝ᵥ (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))| * 2⁻¹ := by
      simp only [dotProduct, Finset.sum_apply, mul_eq_mul_right_iff, inv_eq_zero,
        OfNat.ofNat_ne_zero, or_false, mul_sum]
      congr
      funext x
      congr
      funext y
      ring_nf
    _ = ‖⟪(WithLp.equiv 2 ((Fin n → ZMod 2) → ℝ)).symm a,
        (WithLp.equiv 2 _).symm (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))⟫_ℝ‖ * 2⁻¹ := rfl
    _ ≤ ‖(WithLp.equiv 2 ((Fin n → ZMod 2) → ℝ)).symm a‖ *
      ‖(WithLp.equiv 2 _).symm (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))‖ * 2⁻¹ := by
          apply mul_le_mul_of_nonneg_right
          apply norm_inner_le_norm -- Cauchy-Schwartz
          simp only [inv_nonneg]
          exact zero_le_two
    _ ≤ 2^(-k/2 : ℝ) * ‖(WithLp.equiv 2 _).symm
          (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))‖ * 2⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_right
      apply min_entropy_l2_norm
      assumption
      apply norm_nonneg
      simp only [inv_nonneg]
      exact zero_le_two
    _ ≤ 2^(-k/2 : ℝ) * 2^(n/2 - k/2 : ℝ) * 2⁻¹ := by
      apply mul_le_mul_of_nonneg_right
      apply mul_le_mul_of_nonneg_left
      calc ‖(WithLp.equiv 2 _).symm (∑ x, (fun y => (-1) ^ ZMod.val (y ⬝ᵥ x) * b x))‖
        _ = sqrt (∑ y, (∑ x, (-1) ^ ZMod.val (y ⬝ᵥ x) * b x)^2) := by
          simp [EuclideanSpace.norm_eq]
        _ = sqrt (∑ y, ∑ x, ∑ z, ((-1) ^ ZMod.val (y ⬝ᵥ x) * b x) *
            ((-1) ^ ZMod.val (y ⬝ᵥ z) * b z)) := by simp [sq, sum_mul_sum]
        _ = sqrt (∑ x, ∑ z, ∑ y, ((-1) ^ ZMod.val (y ⬝ᵥ x) * b x) *
            ((-1) ^ ZMod.val (y ⬝ᵥ z) * b z)) := by
          rw [sum_comm]
          congr
          congr
          funext
          rw [sum_comm]
        _ = sqrt (∑ x, ∑ z, b x * b z * ∑ y, (-1) ^ ZMod.val (y ⬝ᵥ x) * (-1) ^ ZMod.val (y ⬝ᵥ z)) := by
          congr
          congr; funext; congr; funext
          ring_nf
          simp [mul_sum, mul_assoc]
        _ = sqrt (∑ x, b x * b x * 2^(n:ℝ)) := by
          congr
          funext x
          rw [sum_eq_add_sum_diff_singleton (i := x)]
          have : ∑ x_1 in univ \ {x}, b x * b x_1 * ∑ y, (-1) ^ ZMod.val (y ⬝ᵥ x) *
            (-1) ^ ZMod.val (y ⬝ᵥ x_1) = 0 := by
            apply sum_eq_zero
            intro z p
            simp
            right
            have D : x ≠ z := by aesop
            exact inner_product_orthogonal n x z D
          rw [this]
          simp
          left
          conv =>
            lhs
            rhs
            intro y
            rw [←sq, ←pow_mul, mul_comm, pow_mul, neg_one_sq, one_pow]
          rw [sum_const]
          simp [card_univ]
          apply mem_univ
        _ = 2^(n/2 : ℝ) * ‖(WithLp.equiv 2 ((Fin n → ZMod 2) → ℝ)).symm b‖ := by
          rw [←sum_mul, mul_comm, sqrt_mul, sqrt_eq_rpow, ←rpow_mul]
          simp [EuclideanSpace.norm_eq, sq]
          left
          ring_nf
          exact zero_le_two
          apply rpow_nonneg zero_le_two
        _ ≤ 2^(n/2 : ℝ) * 2^(-k/2 : ℝ) := by
          apply mul_le_mul_of_nonneg_left
          apply min_entropy_l2_norm
          assumption
          apply rpow_nonneg zero_le_two
        _ = 2^(n/2-k/2 : ℝ) := by rw [←rpow_add]; congr; ring; exact zero_lt_two
      apply rpow_nonneg zero_le_two
      simp
    _ = (2^(n/2 - k - 1 : ℝ)) := by simp [←rpow_neg_one, ←rpow_add, ←rpow_add]; congr 1; ring

#print axioms inner_product_extractor
#check inner_product_extractor
