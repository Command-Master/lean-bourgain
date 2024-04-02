import Pseudorandom.SD
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Prereqs.Discrete.DFT.Compact
import LeanAPAP.Prereqs.Expect.Basic

open Classical Real Finset BigOps

variable
   {α : Type*} [αnonempty: Nonempty α] [Fintype α] [AddCommGroup α]
   {β : Type*} [Nonempty β] [Fintype β] [AddCommGroup β]
   [RCLike 𝕜]
   (a b : α → 𝕜)

open scoped NNReal

-- The DFT isn't normalized.
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

variable
   (a b : α → ℝ)

theorem L1_le_card_rpow_mul_dft_norm :
    ‖a‖_[1] ≤ ((Fintype.card α)^(3/2 : ℝ) : ℝ) * ‖cft (a ·)‖_[⊤] :=
  calc
    ‖a‖_[1] ≤ Real.sqrt (Fintype.card α) * ‖a‖_[(2 : NNReal)] := l1Norm_le_sqrt_card_mul_l2Norm ..
    _ = (Fintype.card α) * ‖a‖ₙ_[2] := by
      rw [lpNorm_eq_card_rpow_mul_nlpNorm]
      rw [← mul_assoc]
      congr
      rw [Real.sqrt_eq_rpow, ← rpow_add]
      norm_num
      simp [Fintype.card_pos]
      norm_num
    _ = (Fintype.card α) * ‖cft (a ·)‖_[2] := by
      congr
      rw [l2Norm_cft, nlpNorm_eq_expect', nlpNorm_eq_expect']
      congr
      ext
      simp
      simp
      simp
    _ ≤ (Fintype.card α) * (Real.sqrt (Fintype.card α) * ‖cft (a ·)‖_[⊤]) := by
      gcongr
      rw [Real.sqrt_eq_rpow]
      convert lpNorm_le_card_rpow_mul_linftyNorm (cft (a ·)) 2 (by norm_num) using 3
      simp
      simp
    _ = ((Fintype.card α)^(3/2 : ℝ) : ℝ) * ‖cft (a ·)‖_[⊤] := by
      rw [sqrt_eq_rpow, ← mul_assoc, ← rpow_one_add']
      congr 1
      norm_num
      simp
      norm_num

lemma lemma43 (t : ℝ) (ε : ℝ)
    (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖dft (a ·) χ‖ ≤ ε)
    (σ : α → β) (h₂ : ∀ χ : AddChar β ℂ,
      ‖cft (χ ∘ σ)‖_[1] ≤ t / (Fintype.card α)
    ):
    ‖σ # a - σ # (fun (x : α) => 1 / (Fintype.card α : ℝ))‖_[1] ≤ t * ε * Real.sqrt (Fintype.card β)
  := by

  sorry

variable (n m : ℕ+) (hₘ : m ≤ n)

local notation "α" => ZMod n
local notation "β" => ZMod m

def abelianC : ℝ := 1

theorem XOR_abelian (ε : ℝ≥0)
  (a : FinPMF α) (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖dft (a ·) χ‖ ≤ ε) :
  SD (a.apply fun x => (x.val : β)) (Uniform ⟨univ, univ_nonempty⟩) ≤
    abelianC * (ε * Real.sqrt m * Real.log n + m / n) := by

  sorry
