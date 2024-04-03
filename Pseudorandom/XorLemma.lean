import Pseudorandom.SD
import Mathlib.RingTheory.RootsOfUnity.Complex
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

lemma lemma43 (t ε : NNReal)
    (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖cft (a ·) χ‖ ≤ ε / (Fintype.card α))
    (σ : α → β) (h₂ : ∀ χ : AddChar β ℂ,
      ‖cft (χ ∘ σ)‖_[1] ≤ t
    ):
    ‖σ # a - σ # (Function.const α (𝔼 x, a x))‖_[1] ≤ t * ε * Real.sqrt (Fintype.card β)
  := by
  suffices ‖cft (fun x => (σ # a - σ # (Function.const α (𝔼 x, a x))) x)‖_[⊤] ≤ t * ε / (Fintype.card β) by
    calc ‖σ # a - σ # (Function.const α (𝔼 x, a x))‖_[1]
      _ ≤ (Fintype.card β)^(3/2 : ℝ) * ‖cft (fun x => (σ # a - σ # (Function.const α (𝔼 x, a x))) x)‖_[⊤] := L1_le_card_rpow_mul_dft_norm _
      _ ≤ (Fintype.card β)^(3/2 : ℝ) * (t * ε / (Fintype.card β)) := by gcongr
      _ = t * ε * ((Fintype.card β)^(3/2 : ℝ) / (Fintype.card β)) := by ring
      _ = t * ε * Real.sqrt (Fintype.card β) := by
        rw [sqrt_eq_rpow, ← rpow_sub_one]
        norm_num
        simp
  rw [linftyNorm_eq_ciSup]
  apply ciSup_le
  intro χ
  dsimp only [cft_apply, nl2Inner_eq_expect]
  simp_rw [← transfer_sub]
  change ‖expect _ fun i => _ * (Complex.ofReal ∘ _) i‖ ≤ _
  simp_rw [comp_transfer]
  conv =>
    lhs
    rhs
    rhs
    intro
    rw [mul_comm]
  rw [transfer_expect]
  simp_rw [mul_comm]
  rw [← nl2Inner_eq_expect]
  by_cases he : χ = 0
  · simp only [he, AddChar.one_apply, Function.comp_apply, Pi.sub_apply, map_sub,
      Complex.ofReal_eq_coe, map_div₀, map_sum, map_natCast, Complex.norm_eq_abs]
    change Complex.abs (_ • nl2Inner (Function.const α 1) _) ≤ _
    rw [nl2Inner_const_left]
    simp [expect_sub_distrib]
    positivity
  · calc ‖(Fintype.card α / Fintype.card β : NNRat) • nl2Inner (χ ∘ σ) (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x)))‖
      _ = (Fintype.card α / Fintype.card β : ℝ) * ‖nl2Inner (χ ∘ σ) (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x)))‖ := by
        rw [← nnratCast_smul_eq_nnqsmul ℝ]
        simp
      _ = (Fintype.card α / Fintype.card β : ℝ) * ‖l2Inner (cft (χ ∘ σ)) (cft (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x))))‖ := by
        rw [l2Inner_cft]
      _ ≤ (Fintype.card α / Fintype.card β : ℝ) * (‖cft (χ ∘ σ)‖_[1] * ‖cft (⇑Complex.ofReal ∘ (a - Function.const α (expect univ fun x => a x)))‖_[⊤]) := by
        gcongr
        apply l2Inner_le_l1Norm_mul_linftyNorm
      _ ≤ (Fintype.card α / Fintype.card β : ℝ) * (t * (ε / (Fintype.card α))) := by
        gcongr
        apply h₂
        rw [linftyNorm_eq_ciSup]
        apply ciSup_le
        intro ψ
        by_cases hψ : ψ = 0
        · simp only [map_comp_sub, Function.comp_const, Complex.ofReal_eq_coe,
          Complex.ofReal_expect, hψ, cft_apply, AddChar.coe_zero, Complex.norm_eq_abs]
          change Complex.abs (nl2Inner (Function.const α 1) _) ≤ _
          rw [nl2Inner_const_left]
          simp [expect_sub_distrib]
          positivity
        · simp only [map_comp_sub, Function.comp_const, Complex.ofReal_eq_coe,
          Complex.ofReal_expect, cft_sub, Pi.sub_apply]
          rw [cft_const]
          simp only [sub_zero]
          apply h
          exact (AddChar.isNontrivial_iff_ne_trivial _).mpr hψ
          exact hψ
      _ = t * ε / (Fintype.card β) := by
        field_simp
        ring_nf


variable (n m : ℕ+) (hₘ : m ≤ n)

local notation "α" => ZMod n
local notation "β" => ZMod m
def lemma44C : ℝ := 1

lemma range_eq_zmod_image : range ↑n = image (fun t => ZMod.val t) (univ : Finset α) := by
  ext x
  simp only [mem_range, mem_image, mem_univ, true_and]
  constructor
  intro v
  exists x
  simp only [ZMod.val_nat_cast]
  apply Nat.mod_eq_of_lt v
  rintro ⟨a, ha⟩
  rw [← ha]
  apply ZMod.val_lt

theorem lemma44 (χ : AddChar β ℂ) : ‖cft (χ ∘ (fun x : α => (x.val : β)))‖_[1] ≤ lemma44C * Real.log n := by
  simp_rw [l1Norm_eq_sum, cft_apply, nl2Inner, expect]
  simp only [Function.comp_apply, ← nnratCast_smul_eq_nnqsmul ℂ, NNRat.cast_inv, NNRat.cast_natCast,
    smul_eq_mul, norm_mul, norm_inv, Complex.norm_nat]
  simp_rw [← AddChar.map_neg_eq_conj, ← mul_sum]
  let w := (AddChar.zmodAddEquiv (n := m) (by simp)).symm χ
  have (y) : χ y = (AddChar.zmod m w) y := by
    have : χ = AddChar.zmodAddEquiv (n := m) (by simp) w := by unfold_let w; simp
    simp [this]
    rfl
  simp_rw [this]
  rw [← Equiv.sum_comp (ι := α) (κ := AddChar α ℂ) (AddChar.zmodAddEquiv (n := n) (by simp))]
  conv =>
    lhs
    rhs
    rhs
    intro t
    rhs
    rhs
    intro x
    tactic =>
      simp only [EquivLike.coe_coe, AddChar.zmodAddEquiv_apply]
      change ((AddChar.zmod n t) (-x) * (AddChar.zmod m w) (x.val) : circle) = (_ : ℂ)
      convert_to ((AddChar.zmod n (t.val : ℤ)) (- x.val : ℤ) * (AddChar.zmod m (w.val : ℤ)) (x.val : ℤ) : circle) = (_ : ℂ)
      congr <;> simp
      simp only [AddChar.zmod_apply]
      simp only [ZMod.nat_cast_val, ZMod.int_cast_cast, Int.cast_neg, mul_neg, ←
        AddChar.map_add_mul]
      convert_to Circle.e (x.val * (w.val * n - t.val * m) / (n * m)) = (_ : ℂ)
      congr
      simp only [ZMod.nat_cast_val]
      field_simp
      ring
      rfl
  calc (univ.card : ℝ)⁻¹ * ∑ t : α, ‖∑ x : α, (Circle.e (x.val * (w.val * n - t.val * m) / (n * m)) : ℂ)‖
    _ = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, ‖∑ x : α,
        (Circle.e (x.val * (w.val * n - t * m) / (n * m)) : ℂ)‖ := by
      congr 1
      simp [card_univ]
      apply Eq.symm
      convert Finset.sum_image ?_
      apply range_eq_zmod_image
      intro x _ y _ v
      apply ZMod.val_injective n v
    _ = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, ‖∑ x ∈ Finset.range n,
        (Circle.e (x * (w.val * n - t * m) / (n * m)) : ℂ)‖ := by
      congr
      ext t
      congr 1
      apply Eq.symm
      convert Finset.sum_image ?_
      apply range_eq_zmod_image
      intro x _ y _ v
      apply ZMod.val_injective n v
    _ ≤ lemma44C * Real.log n := sorry


-- theorem XOR_abelian (ε : ℝ≥0)
--   (a : FinPMF α) (h : ∀ χ : AddChar α ℂ, (AddChar.IsNontrivial χ) → ‖dft (a ·) χ‖ ≤ ε) :
--   SD (a.apply fun x => (x.val : β)) (Uniform ⟨univ, univ_nonempty⟩) ≤
--     abelianC * (ε * Real.sqrt m * Real.log n + m / n) := by

--   sorry
