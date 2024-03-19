import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Pseudorandom.PDF
import Pseudorandom.SD

open Classical Real Finset BigOperators RealInnerProductSpace

attribute [local simp] Set.Finite.bddAbove Set.finite_range card_univ

variable
   {α : Type u1} [Nonempty α] [Fintype α]
   {β : Type u2} [Nonempty β] [Fintype β]
   (a b : FinPMF α)

noncomputable def min_entropy : ℝ :=
  -(logb 2 (⨆ x : α, a x))

lemma min_entropy_le (k : ℝ) : min_entropy a ≥ k ↔ ∀ i, a i ≤ 2^(-k) := by
  constructor
  intros p i
  calc
    a i ≤ ⨆ x, a x := by apply le_ciSup; simp
    _ = 2^(logb 2 (⨆ x, a x)) := by rw [rpow_logb]; aesop; aesop; apply FinPMF.not_all_zero
    _ = 2^(-min_entropy a) := by simp [min_entropy]
    _ ≤ 2^(-k) := by apply rpow_le_rpow_of_exponent_le <;> linarith
  intro p
  simp [min_entropy]
  rw [le_neg]
  rw [←logb_rpow (x := -k) zero_lt_two (OfNat.ofNat_ne_one 2)]
  apply logb_le_logb_of_le
  exact one_lt_two
  apply FinPMF.not_all_zero
  exact ciSup_le p

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
noncomputable def two_extractor {γ : Type u3} [Nonempty γ] [Fintype γ]
  (h : (α × β) → γ) (k : ℕ) (ε : ℝ) : Prop :=
  ∀ a, ∀ b, (min_entropy a ≥ k ∧ min_entropy b ≥ k) → (SD ((a * b).apply h) (Uniform ⟨univ, univ_nonempty⟩) ≤ ε)
