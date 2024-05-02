import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Pseudorandom.PMF
import Pseudorandom.SD

open Classical Real Finset BigOperators RealInnerProductSpace

attribute [local simp] Set.Finite.bddAbove Set.finite_range card_univ

variable
   {α : Type*} [Nonempty α] [Fintype α]
   {β : Type*} [Nonempty β] [Fintype β]
   (a b : FinPMF α)
   {x : α}

noncomputable def max_val : ℝ :=
  ⨆ x : α, a x

@[simp]
lemma le_max_val : a x ≤ max_val a := by
  apply le_ciSup
  simp

lemma max_val_le_one : max_val a ≤ 1 := by
  apply ciSup_le
  intro x
  calc a x
    _ ≤ ∑ x, a x := by apply single_le_sum; intros; simp; simp
    _ = 1 := by simp

-- The maximum value a PMF takes is greater than zero
lemma card_inv_le_max_val : (Fintype.card α : ℝ)⁻¹ ≤ max_val a := by
  rw [inv_pos_le_iff_one_le_mul']
  calc
    1 = ∑ x, a x := by simp
    _ ≤ ∑ __ : α, max_val a := by
      gcongr
      simp
    _ = (Fintype.card α) * max_val a := by
      simp
  simp [Fintype.card_pos]

lemma zero_lt_max_val : 0 < max_val a := calc
  0 < (Fintype.card α : ℝ)⁻¹ := by simp [Fintype.card_pos]
  _ ≤ max_val a := card_inv_le_max_val ..

noncomputable def min_entropy : ℝ :=
  -(logb 2 (max_val a))

lemma two_pow_neg_min_entropy_eq_max_val :
  2^(-min_entropy a) = max_val a := by
  unfold min_entropy
  simp
  rw [rpow_logb]
  repeat norm_num
  apply zero_lt_max_val

lemma min_entropy_of_max_val_le (k : ℝ) :
  max_val a ≤ (2^k)⁻¹ ↔ k ≤ min_entropy a := by
    rw [← two_pow_neg_min_entropy_eq_max_val]
    simp [rpow_neg]
    rw [inv_le_inv]
    have : 1 < (2 : ℝ) := by norm_num
    simp
    apply rpow_pos_of_pos
    norm_num
    apply rpow_pos_of_pos
    norm_num

lemma min_entropy_le (k : ℝ) : min_entropy a ≥ k ↔ ∀ i, a i ≤ 2^(-k) := by
  rw [min_entropy]
  rw [ge_iff_le]
  conv =>
    lhs
    rw [←rpow_le_rpow_left_iff one_lt_two]
  rw [rpow_neg, rpow_logb zero_lt_two (by norm_num), ← le_inv, ← rpow_neg]
  simp only [max_val]
  apply ciSup_le_iff
  simp
  exact zero_le_two
  apply zero_lt_max_val
  exact rpow_pos_of_pos zero_lt_two k
  apply zero_lt_max_val
  exact zero_le_two

-- min entropy implies a bound on the L2 norm of the function.
lemma min_entropy_l2_norm (k : ℕ) (a : FinPMF α) (h : ↑k ≤ min_entropy a):
  ‖(WithLp.equiv 2 (α → ℝ)).symm a‖ ≤ 2 ^ (-k/2 : ℝ) := by
    rw [PiLp.norm_eq_sum]
    simp
    suffices ∑ x : α, a x ^ 2 ≤ 2 ^ (-k : ℝ) by
      rw [←one_div, div_eq_mul_one_div (-k : ℝ) 2, rpow_mul]
      apply rpow_le_rpow
      apply sum_nonneg
      repeat aesop
    calc
      ∑ x : α, a x ^ 2 ≤ ∑ x : α, a x * 2^(-k:ℝ) := by
        apply sum_le_sum
        intro i _
        rw [sq (a i)]
        apply mul_le_mul_of_nonneg_left
        apply (min_entropy_le a _).1
        simp_all
        simp
      _ ≤ 2^(-k:ℝ) := by simp [←sum_mul]
    simp


/- A function in an (k, ε)-two extractor if for any two indepndent random variables,
  each with min entropy at least k, the distance of the function from uniformity is
  at most ε.
-/
noncomputable def two_extractor {γ : Type*} [Nonempty γ] [Fintype γ]
  (h : (α × β) → γ) (k : ℝ) (ε : ℝ) : Prop :=
  ∀ a, ∀ b, (min_entropy a ≥ k ∧ min_entropy b ≥ k) → (SD ((a * b).apply h) (Uniform ⟨univ, univ_nonempty⟩) ≤ ε)
