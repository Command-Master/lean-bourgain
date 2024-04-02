import Mathlib.Data.Nat.Prime
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Image
import Mathlib.Data.ZMod.Defs
import Mathlib.Algebra.BigOperators.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Chebyshev
import LeanAPAP.Prereqs.Expect.Basic
import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Data.SetLike.Fintype
import Pseudorandom.Geometry.Lines
import Pseudorandom.Incidence.Constants
import Pseudorandom.Incidence.Claim342
import Pseudorandom.Geometry.Projective
import Pseudorandom.Incidence.IncidenceGrid
set_option autoImplicit false

open Real BigOps Finset

variable (p : ℕ) [Fact p.Prime]

local notation "α" => (ZMod p)

set_option maxHeartbeats 700000

theorem ST_prime_field_proj (β : ℝ) (h : 0 < β) (P : Finset (α × α)) (L : Finset (Line α)) (n : ℕ+)
  (nhₗ : (p^β : ℝ) ≤ n) (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (h₁ : P.card ≤ n) (h₂ : L.card ≤ n)
    (p₁ p₂ : α × α) (neq : p₁ ≠ p₂) (nml₁ : (IntersectionsL p₁ L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
    (nml₂ : (IntersectionsL p₂ L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
    (all_int : ∀ p ∈ P, (∃ l ∈ L, p ∈ l ∧ p₁ ∈ l) ∧ ∃ l ∈ L, p ∈ l ∧ p₂ ∈ l)
    (nl : ∀ p ∈ P, ¬p ∈ Line.of p₁ p₂ neq):
      (Intersections P L).card ≤ (ST_C₇ * n ^ (3/2 - 13/12 * ST_prime_field_eps₄ β) : ℝ)
    := by
  let proj := projective_transform p₁ p₂ neq
  let Pn := P.image (fun (x : α × α) ↦ Vnorm (proj (x.1, x.2, 1)))
  let Ln := L.image (fun x ↦ x.apply proj)
  have : (Intersections P L).card = (Intersections Pn Ln).card := by
    apply Finset.card_congr (fun (p, l) __ => (Vnorm (proj (p.1, p.2, 1)), l.apply proj))
    intros a ha
    simp
    simp [Intersections]
    simp [Intersections] at ha
    constructor
    simp [Pn, Ln]
    constructor
    exists a.1.1, a.1.2
    simp_all
    exists a.2
    simp_all
    rw [←norm_mem]
    simp [Line.apply, instSetLike]
    exact ha.2
    apply non_erasing
    apply nl
    exact ha.1.1
    intros a b ha hb
    simp
    simp [Intersections] at ha
    simp [Intersections] at hb
    intros eq1 eq2
    apply vnorm_eq_vnorm at eq1
    have ⟨r, muleq⟩ := eq1 (non_erasing p₁ p₂ a.1 neq (nl a.1 ha.1.1)) (non_erasing p₁ p₂ b.1 neq (nl b.1 hb.1.1))
    rw [←LinearEquiv.map_smul] at muleq
    apply LinearEquiv.injective at muleq
    simp at muleq
    have := muleq.2.2
    rw [this] at muleq
    simp at muleq
    apply apply_injective at eq2
    aesop
    intros b hb
    simp
    simp [Pn, Ln, Intersections] at hb
    have ⟨⟨⟨a1, a2, ha⟩, ⟨l, hl⟩⟩, hi⟩ := hb
    exists a1, a2, l
    constructor
    simp [Intersections]
    constructor
    exact ⟨ha.1, hl.1⟩
    rw [←ha.2, ←hl.2] at hi
    simp [mem2]
    change (a1, a2, (1: α)) ∈ (l : (Set _))
    rw [←norm_mem] at hi
    simp [Line.apply] at hi
    apply Submodule.mem_map.mp at hi
    have ⟨y, hy1, hy2⟩ := hi
    simp at hy2
    rw [hy2] at hy1
    exact hy1
    apply non_erasing (x := (a1, a2))
    apply nl
    exact ha.1
    simp_all
  let A := Pn.image (fun x => x.1)
  let B := Pn.image (fun x => x.2)
  have As : A.card ≤ (IntersectionsL p₂ L).card := by
    simp [A, Pn, image_image]
    change (P.image (fun x => (Vnorm (proj (x.1, x.2, 1))).1)).card ≤ (IntersectionsL p₂ L).card
    apply Finset.card_le_card_of_inj_on (fun x => if h : x ∈ P.image (fun x => (Vnorm (proj (x.1, x.2, 1))).1) then
      Classical.choose (all_int (Classical.choose (Finset.mem_image.mp h))
        (Classical.choose_spec (Finset.mem_image.mp h)).1).2
    else Line.infinity α)
    intro a ha
    simp [ha]
    have := Classical.choose_spec (all_int (Classical.choose (Finset.mem_image.mp ha)) (Classical.choose_spec (Finset.mem_image.mp ha)).1).2
    simp [IntersectionsL]
    exact ⟨this.1, this.2.2⟩
    intro a₁ ha₁ a₂ ha₂ eq
    let v₁ := Classical.choose (Finset.mem_image.mp ha₁)
    have pr₁ : v₁ ∈ P ∧ (Vnorm (proj (v₁.1, v₁.2, 1))).1 = a₁ := Classical.choose_spec (Finset.mem_image.mp ha₁)
    let c₁ := Classical.choose (all_int v₁ pr₁.1).2
    have pc1 : c₁ ∈ L ∧ v₁ ∈ c₁ ∧ p₂ ∈ c₁ := Classical.choose_spec (all_int v₁ pr₁.1).2
    let v₂ := Classical.choose (Finset.mem_image.mp ha₂)
    have pr₂ : v₂ ∈ P ∧ (Vnorm (proj (v₂.1, v₂.2, 1))).1 = a₂ := Classical.choose_spec (Finset.mem_image.mp ha₂)
    let c₂ := Classical.choose (all_int v₂ pr₂.1).2
    have pc2 : c₂ ∈ L ∧ v₂ ∈ c₂ ∧ p₂ ∈ c₂ := Classical.choose_spec (all_int v₂ pr₂.1).2
    -- have vc₂
    simp_all
    change c₁ = c₂ at eq
    simp [←eq] at pc2
    let l := c₁.apply proj
    have p₁m : proj (p₂.1, p₂.2, 1) ∈ (l : Set _) := by
      simp [l, Line.apply]
      apply Submodule.mem_map.mpr
      exists (p₂.1, p₂.2, 1)
      simp
      exact pc2.2.2
    rw [project_q] at p₁m
    rw [←pr₁.2, ←pr₂.2]
    apply Line.vert_constant l
    rw [←norm_mem]
    simp [l, Line.apply]
    apply Submodule.mem_map.mp
    simp
    exact pc1.2.1
    apply non_erasing
    apply nl
    exact pr₁.1

    rw [←norm_mem]
    simp [l, Line.apply]
    apply Submodule.mem_map.mp
    simp
    exact pc2.2.1
    apply non_erasing
    apply nl
    exact pr₂.1

    exact p₁m
  have Bs : B.card ≤ (IntersectionsL p₁ L).card := by
    simp [B, Pn, image_image]
    change (P.image (fun x => (Vnorm (proj (x.1, x.2, 1))).2)).card ≤ (IntersectionsL p₁ L).card
    apply Finset.card_le_card_of_inj_on (fun x => if h : x ∈ P.image (fun x => (Vnorm (proj (x.1, x.2, 1))).2) then
      Classical.choose (all_int (Classical.choose (Finset.mem_image.mp h))
        (Classical.choose_spec (Finset.mem_image.mp h)).1).1
    else Line.infinity α)
    intro a ha
    simp [ha]
    have := Classical.choose_spec (all_int (Classical.choose (Finset.mem_image.mp ha)) (Classical.choose_spec (Finset.mem_image.mp ha)).1).1
    simp [IntersectionsL]
    exact ⟨this.1, this.2.2⟩
    intro a₁ ha₁ a₂ ha₂ eq
    let v₁ := Classical.choose (Finset.mem_image.mp ha₁)
    have pr₁ : v₁ ∈ P ∧ (Vnorm (proj (v₁.1, v₁.2, 1))).2 = a₁ := Classical.choose_spec (Finset.mem_image.mp ha₁)
    let c₁ := Classical.choose (all_int v₁ pr₁.1).1
    have pc1 : c₁ ∈ L ∧ v₁ ∈ c₁ ∧ p₁ ∈ c₁ := Classical.choose_spec (all_int v₁ pr₁.1).1
    let v₂ := Classical.choose (Finset.mem_image.mp ha₂)
    have pr₂ : v₂ ∈ P ∧ (Vnorm (proj (v₂.1, v₂.2, 1))).2 = a₂ := Classical.choose_spec (Finset.mem_image.mp ha₂)
    let c₂ := Classical.choose (all_int v₂ pr₂.1).1
    have pc2 : c₂ ∈ L ∧ v₂ ∈ c₂ ∧ p₁ ∈ c₂ := Classical.choose_spec (all_int v₂ pr₂.1).1
    simp_all
    change c₁ = c₂ at eq
    simp [←eq] at pc2
    let l := c₁.apply proj
    have p₂m : proj (p₁.1, p₁.2, 1) ∈ (l : Set _) := by
      simp [l, Line.apply]
      apply Submodule.mem_map.mpr
      exists (p₁.1, p₁.2, 1)
      simp
      exact pc2.2.2
    rw [project_p] at p₂m
    rw [←pr₁.2, ←pr₂.2]
    apply Line.horiz_constant l

    rw [←norm_mem]
    simp [l, Line.apply]
    apply Submodule.mem_map.mp
    simp
    exact pc1.2.1
    apply non_erasing
    apply nl
    exact pr₁.1

    rw [←norm_mem]
    simp [l, Line.apply]
    apply Submodule.mem_map.mp
    simp
    exact pc2.2.1
    apply non_erasing
    apply nl
    exact pr₂.1

    exact p₂m
  rw [this]
  calc ((Intersections Pn Ln).card : ℝ)
    _ ≤ (Intersections (A ×ˢ B) Ln).card := by
      simp [Intersections]
      gcongr
      rw [subset_iff]
      intros x hx
      cases x
      rename_i fst snd
      simp_all
      simp [A, B]
      constructor
      exists fst.2
      exact hx.1
      exists fst.1
      exact hx.1
    _ ≤ SG_C * n ^ (3/2 - SG_eps β) := by
      apply ST_grid <;> try assumption
      calc
        (A.card : ℝ) ≤ (IntersectionsL p₂ L).card := by norm_cast
        _ ≤ _ := nml₂
      calc
        (B.card : ℝ) ≤ (IntersectionsL p₁ L).card := by norm_cast
        _ ≤ _ := nml₁
      calc
        Ln.card ≤ L.card := Finset.card_image_le ..
        _ ≤ n := h₂
    _ = ST_C₇ * n ^ (3/2 - 13/12 * ST_prime_field_eps₄ β) := by
      simp [ST_C₇, ST_prime_field_eps₄]
      left
      ring_nf


theorem ST_prime_field_aux (β : ℝ) (h : 0 < β) (P : Finset (α × α)) (L : Finset (Line α)) (n : ℕ+)
  (nhₗ : (p^β : ℝ) ≤ n) (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (h₁ : P.card ≤ n) (h₂ : L.card ≤ n)
    -- (hb : ∀ l ∈ L, (IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
    (hc : ∀ l ∈ P, (n^(1/2 - ST_prime_field_eps₂ β) : ℝ) ≤ (IntersectionsL l L).card)
    (hd : ∀ l ∈ P, (IntersectionsL l L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
  :
  (Intersections P L).card ≤ (ST_C₅ * n ^ (3/2 - ST_prime_field_eps₃ β) : ℝ) := by
  by_contra! nh
  have ⟨p₁, hp₁, p₂, hp₂, neq, large'⟩ := claim_342 β h P L n h₁ h₂ nh hd
  let P' := P.filter (fun x => (∃ l ∈ L, x ∈ l ∧ p₁ ∈ l) ∧ ∃ l ∈ L, x ∈ l ∧ p₂ ∈ l)
  have large : (ST_C₆ * n ^ (1 - ST_prime_field_eps₄ β) : ℝ) < P'.card := by
    simp [P', large']
  clear large'
  have nh₂ := calc ((Intersections P' L).card : ℝ)
    _ = ∑ x ∈ P', (IntersectionsL x L).card := by norm_cast; apply IntersectionsL_sum
    _ ≥ ∑ x ∈ P', (n^(1/2 - ST_prime_field_eps₂ β) : ℝ) := by
      simp [-one_div, -sum_const]
      gcongr with i hi
      apply hc
      simp [P'] at hi
      exact hi.1
    _ = P'.card * n^(1/2 - ST_prime_field_eps₂ β) := by simp
    _ > ST_C₆ * n ^ (1 - ST_prime_field_eps₄ β) * n^(1/2 - ST_prime_field_eps₂ β) := by
      gcongr
      apply rpow_pos_of_pos
      simp
    _ = ST_C₆ * (n ^ (1 - ST_prime_field_eps₄ β) * n^(1/2 - ST_prime_field_eps₂ β)) := by ring
    _ = ST_C₆ * n ^ (3/2 - 13/12 * ST_prime_field_eps₄ β) := by
      congr
      rw [←rpow_add]
      congr 1
      simp [ST_prime_field_eps₂, ST_prime_field_eps₃]
      ring
      simp
  let l := Line.of p₁ p₂ neq
  let P'' := P' \ (P'.filter (fun x => x ∈ l))
  have nh₃ := calc ((Intersections P'' L).card : ℝ)
    _ = ∑ p ∈ P'', (IntersectionsL p L).card := by norm_cast; apply IntersectionsL_sum
    _ = ∑ p ∈ P', (IntersectionsL p L).card -
        ∑ p ∈ (P'.filter (fun x => x ∈ l)), (IntersectionsL p L).card := by
      simp [P'']
    _ = (Intersections P' L).card - (Intersections (P'.filter (fun x => x ∈ l)) L).card := by
      simp [IntersectionsL_sum]
    _ > ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) - (Intersections (P'.filter (fun x => x ∈ l)) L).card := by
      gcongr
    _ = ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) - ∑ l₂ ∈ L, (IntersectionsP (P'.filter (fun x => x ∈ l)) l₂).card := by
      congr
      rw [IntersectionsP_sum]
    _ ≥ ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) - ∑ l₂ ∈ (L ∪ {l}), (IntersectionsP (P'.filter (fun x => x ∈ l)) l₂).card := by
      gcongr
      apply sum_le_sum_of_subset_of_nonneg
      apply subset_union_left
      intros
      simp
    _ = ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) -
      (∑ l₂ ∈ L \ {l}, (IntersectionsP (P'.filter (fun x => x ∈ l)) l₂).card + (IntersectionsP (P'.filter (fun x => x ∈ l)) l).card) := by
      congr
      norm_cast
      rw [Finset.sum_eq_sum_diff_singleton_add (i := l)]
      congr 2
      apply union_sdiff_right
      simp
    _ = ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) -
      (∑ l₂ ∈ L \ {l}, ((P'.filter (fun x => x ∈ l)).filter (fun x => x ∈ l₂)).card + (IntersectionsP (P'.filter (fun x => x ∈ l)) l).card) := by
      rfl
    _ = ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) -
      (∑ l₂ ∈ L \ {l}, (P'.filter (fun x => x ∈ l ∧ x ∈ l₂)).card + (IntersectionsP (P'.filter (fun x => x ∈ l)) l).card) := by
      congr
      ext l₂
      rw [filter_filter]
    _ ≥ ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) -
      (∑ l₂ ∈ L \ {l}, (univ.filter (fun x => x ∈ l ∧ x ∈ l₂)).card + P'.card) := by
      gcongr
      simp
      simp [IntersectionsP]
    _ ≥ ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) -
      (∑ l₂ ∈ L \ {l}, 1 + P.card) := by
      gcongr
      norm_cast
      apply sum_le_sum
      intro i hi
      apply line_intersect
      apply Ne.symm
      simp at hi
      simp [hi]
      simp [P']
    _ ≥ ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) -
      (n + n) := by
      gcongr
      simp
      norm_cast
      calc
        (L \ {l}).card ≤ L.card := by gcongr; simp
        _ ≤ n := by assumption
    _ ≥ ST_C₆ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) -
      (n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) + n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β)) := by
      gcongr
      repeat {
      conv =>
        lhs
        apply (Real.rpow_one _).symm
      apply Real.rpow_le_rpow_of_exponent_le
      norm_cast
      simp
      apply lemma4
      }
    _ = (ST_C₆ - 2) * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) := by ring
    _ = ST_C₇ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) := by simp [ST_C₆]
  suffices ((Intersections P'' L).card : ℝ) ≤ ST_C₇ * n ^ (3 / 2 - 13 / 12 * ST_prime_field_eps₄ β) by linarith
  apply ST_prime_field_proj (p₁ := p₁) (p₂ := p₂) <;> try assumption
  calc
    P''.card ≤ P'.card := by gcongr; simp [P'']
    _ ≤ P.card := by gcongr; simp [P']
    _ ≤ n := by assumption
  apply hd
  assumption
  apply hd
  assumption
  intro p ph
  have : p ∈ P' := by simp_all [P'']
  simp [P'] at this
  exact this.2
  intro p ph
  simp [P''] at ph
  simp_all

theorem ST_prime_field_aux₂' (β : ℝ) (h : 0 < β) (P : Finset (α × α)) (L : Finset (Line α)) (n : ℕ+)
  (nhₗ : (p^β : ℝ) ≤ n) (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (h₁ : P.card ≤ n) (h₂ : L.card ≤ n)
    -- (hb : ∀ l ∈ L, (IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
    (hc : ∀ l ∈ P, (n^(1/2 - ST_prime_field_eps₂ β) : ℝ) ≤ (IntersectionsL l L).card)
  :
  (Intersections P L).card ≤ (ST_C₄ * n ^ (3/2 - ST_prime_field_eps₂ β) : ℝ) := by
  by_contra! nh
  have neq0 : (n : ℝ) ≠ 0 := by simp
  have : (Intersections P L).card^2 ≤ L.card * P.card * (L.card + P.card) := by apply CS_UB
  let P₁ := P.filter (fun l => (IntersectionsL l L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))
  have := calc (ST_C₅ * n ^ (3/2 - ST_prime_field_eps₃ β) : ℝ)
    _ ≥ (Intersections P₁ L).card := by
      rw [ge_iff_le]
      apply ST_prime_field_aux <;> try assumption
      calc
        P₁.card ≤ P.card := by apply Finset.card_le_card; simp [P₁]
        _ ≤ n := by assumption
      -- intro l hl
      -- calc ((IntersectionsP P₁ l).card : ℝ)
      --   _ ≤ (IntersectionsP P l).card := by norm_cast; apply Finset.card_le_card; apply IntP_subset_of_subset; simp [P₁]
      --   _ ≤ 4 * n^(1/2 + 2*ST_prime_field_eps β) := by apply hb; assumption
      intros
      apply hc
      simp_all [P₁]
      intros
      simp_all [P₁]
    _ = ∑ y in P₁, (IntersectionsL y L).card := by norm_cast; apply IntersectionsL_sum
    _ ≥ ∑ __ in P₁, (n^(1/2 - ST_prime_field_eps₂ β) : ℝ) := by rw [ge_iff_le, Nat.cast_sum]; gcongr with i; exact hc i (by simp_all [P₁])
    _ = P₁.card * (n^(1/2 - ST_prime_field_eps₂ β) : ℝ) := by simp
    _ = (P.card - (P.filter (fun l => ¬(IntersectionsL l L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))).card) *
      n^(1/2 - ST_prime_field_eps₂ β) := by
      simp [-not_le, P₁]
      left
      apply eq_sub_of_add_eq
      norm_cast
      apply filter_card_add_filter_neg_card_eq_card
    _ ≥ (P.card - n^(1 - 2*ST_prime_field_eps₂ β) * (Real.sqrt 2 / 4)) * n^(1/2 - ST_prime_field_eps₂ β) := by
      gcongr
      calc ((P.filter (fun l => ¬(IntersectionsL l L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))).card : ℝ)
        _ = ∑ x in (P.filter (fun l => ¬(IntersectionsL l L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))), 1 := by simp
        _ ≤ ∑ x in (P.filter (fun l => ¬(IntersectionsL l L).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ))),
          (IntersectionsL x L).card / (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ) := by
          gcongr
          rw [one_le_div]
          apply le_of_lt
          simp_all
          simp
          apply rpow_pos_of_pos
          simp
          -- sorry
        _ ≤ (∑ x in P, (IntersectionsL x L).card) / (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ) := by
          simp [sum_div]
          apply sum_le_sum_of_subset_of_nonneg
          simp
          intros
          apply div_nonneg
          simp
          simp
          apply rpow_nonneg
          simp
          -- sorry
        _ = (Intersections P L).card / (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ) := by congr 1; norm_cast; rw [IntersectionsL_sum]
        _ ≤ Real.sqrt (L.card * P.card * (L.card + P.card)) / (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ) := by
          gcongr
          rw [le_sqrt]
          norm_cast
          simp
          norm_cast
          simp
          -- sorry
        _ ≤ Real.sqrt (n * n * (n+n)) / (4 * n^(1/2 + 2*ST_prime_field_eps₂ β) : ℝ) := by
          gcongr
          apply sqrt_le_sqrt
          gcongr
          -- sorry
        _ = n^(1 - 2*ST_prime_field_eps₂ β) * (Real.sqrt 2 / 4) := by
          simp [←mul_two, sqrt_eq_rpow]
          ring_nf
          rw [mul_rpow, ←rpow_nat_cast, ←rpow_mul, ←rpow_neg]
          ring_nf
          conv =>
            lhs
            lhs
            rw [mul_comm, ←mul_assoc, ←rpow_add]
            · skip
            · tactic => simp
          ring_nf
          repeat simp
          -- sorry
    _ > (n^(1 - 2*ST_prime_field_eps₂ β) * (ST_C₄^2 / 2)  - n^(1 - 2*ST_prime_field_eps₂ β) * (Real.sqrt 2 / 4)) * n^(1/2 - ST_prime_field_eps₂ β) := by
      gcongr
      rw [←gt_iff_lt]
      calc
        (P.card : ℝ) = n * P.card * (n + n) / (2*n*n) := by ring_nf; simp [mul_comm]
        _ ≥ L.card * P.card * (L.card + P.card) / (2*n*n) := by gcongr
        _ ≥ (Intersections P L).card^2 / (2 * n * n) := by gcongr; norm_cast
        _ > (ST_C₄ * n ^ (3/2 - ST_prime_field_eps₂ β))^2 / (2 * n * n) := by gcongr
        _ = n^(1 - 2*ST_prime_field_eps₂ β) * (ST_C₄^2 / 2) := by
          rw [←rpow_nat_cast, mul_rpow, ←rpow_mul]
          ring_nf
          rw [inv_pow, ←rpow_nat_cast, ←rpow_neg]
          conv =>
            lhs
            lhs
            rw [mul_assoc]
            rhs
            rw [←rpow_add]
            · simp
            · tactic => simp
          norm_num
          ring_nf
          simp
          simp
          simp
          apply rpow_nonneg
          simp
    _ = ((ST_C₄^2 / 2) - Real.sqrt 2 / 4) * (n^(1 - 2*ST_prime_field_eps₂ β) * n^(1/2 - ST_prime_field_eps₂ β)) := by
      ring
    _ = ((ST_C₄^2 / 2) - Real.sqrt 2 / 4) * n^(3/2 - 3*ST_prime_field_eps₂ β) := by
      congr
      rw [←rpow_add]
      congr 1
      ring
      simp
    _ = ST_C₅ * n^(3/2 - ST_prime_field_eps₃ β) := by
      congr 2
      simp only [ST_C₄]
      norm_cast
      rw [NNReal.sq_sqrt]
      simp
      ring_nf
      simp [ST_prime_field_eps₂]
      ring
  simp_all

theorem ST_prime_field_aux₂ (β : ℝ) (h : 0 < β) (P : Finset (α × α)) (L : Finset (Line α)) (n : ℕ+)
  (nhₗ : (p^β : ℝ) ≤ n) (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (h₁ : P.card ≤ n) (h₂ : L.card ≤ n)
    (hb : ∀ l ∈ L, (IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  :
  (Intersections P L).card ≤ (ST_C₃ * n ^ (3/2 - ST_prime_field_eps₂ β) : ℝ) := by
  calc
    ((Intersections P L).card : ℝ) = ∑ y in P, (IntersectionsL y L).card := by norm_cast; apply IntersectionsL_sum
    _ = ∑ y in P.filter
          (fun y => (IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ)), (IntersectionsL y L).card +
        ∑ y in P.filter
          (fun y => ¬(IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ)), (IntersectionsL y L).card := by
      norm_cast
      rw [sum_filter_add_sum_filter_not]
    _ ≤ ∑ __ in P.filter
          (fun y => (IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ)), (n^(1/2 - ST_prime_field_eps₂ β) : ℝ) +
        ∑ y in P.filter
          (fun y => ¬(IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ)), (IntersectionsL y L).card := by
      simp only [one_div, Nat.cast_sum, not_le, add_le_add_iff_right]
      gcongr with i ih
      simp_all only [one_div, mem_filter]
    _ ≤ n^(1/2 - ST_prime_field_eps₂ β) * n +
      ∑ y in P.filter
          (fun y => ¬(IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ)), (IntersectionsL y L).card := by
      gcongr ?_ + ?_
      simp only [one_div, sum_const, nsmul_eq_mul]
      rw [mul_comm]
      gcongr
      calc (P.filter (fun y => (IntersectionsL y L).card ≤ (n^(2⁻¹ - ST_prime_field_eps₂ β) : ℝ))).card
        _ ≤ P.card := by apply Finset.card_le_card; simp only [filter_subset]
        _ ≤ n := h₁
      simp only [one_div, not_le, Nat.cast_sum, le_refl]
    _ = n^(3/2 - ST_prime_field_eps₂ β) +
        (Intersections (P.filter (fun y => ¬(IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ))) L).card := by
      congr
      rw [←rpow_add_one]
      congr 1
      ring
      simp only [ne_eq, Nat.cast_eq_zero, PNat.ne_zero, not_false_eq_true]
      rw [IntersectionsL_sum]
    _ ≤ n^(3/2 - ST_prime_field_eps₂ β) + ST_C₄ * n ^ (3/2 - ST_prime_field_eps₂ β) := by
      gcongr
      apply ST_prime_field_aux₂' <;> try assumption
      calc (P.filter (fun y => ¬(IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ))).card
        _ ≤ P.card := by apply Finset.card_le_card; simp
        _ ≤ n := h₁
      -- intro l hl
      -- calc ((IntersectionsP (P.filter (fun y => ¬(IntersectionsL y L).card ≤ (n^(1/2 - ST_prime_field_eps₂ β) : ℝ))) l).card : ℝ)
      --   _ ≤ (IntersectionsP P l).card := by norm_cast; apply Finset.card_le_card; apply IntP_subset_of_subset; simp
      --   _ ≤ 4 * n^(1/2 + 2*ST_prime_field_eps β) := by apply hb; assumption
      intros
      apply le_of_lt
      simp_all
    _ = ST_C₃ * n ^ (3/2 - ST_prime_field_eps₂ β) := by simp [ST_C₃]; ring

theorem ST_prime_field_aux' (β : ℝ) (h : 0 < β) (P : Finset (α × α)) (L : Finset (Line α)) (n : ℕ+)
  (nhₗ : (p^β : ℝ) ≤ n) (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (h₁ : P.card ≤ n) (h₂ : L.card ≤ n)
    (ha : ∀ l ∈ L, (n^(1/2 - ST_prime_field_eps β) : ℝ) ≤ (IntersectionsP P l).card)
  :
  (Intersections P L).card ≤ (ST_C₂ * n ^ (3/2 - ST_prime_field_eps β) : ℝ) := by
  by_contra! nh
  have neq0 : (n : ℝ) ≠ 0 := by simp
  have : (Intersections P L).card^2 ≤ L.card * P.card * (L.card + P.card) := by apply CS_UB
  let L₁ := L.filter (fun l => (IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))
  have := calc (ST_C₃ * n ^ (3/2 - ST_prime_field_eps₂ β) : ℝ)
    _ ≥ (Intersections P L₁).card := by
      rw [ge_iff_le]
      apply ST_prime_field_aux₂ <;> try assumption
      calc
        L₁.card ≤ L.card := by apply Finset.card_le_card; simp [L₁]
        _ ≤ n := by assumption
      intros
      simp_all [L₁]
    _ = ∑ y in L₁, (IntersectionsP P y).card := by norm_cast; apply IntersectionsP_sum
    _ ≥ ∑ y in L₁, (n^(1/2 - ST_prime_field_eps β) : ℝ) := by rw [ge_iff_le, Nat.cast_sum]; gcongr with i; exact ha i (by simp_all [L₁])
    _ = L₁.card * (n^(1/2 - ST_prime_field_eps β) : ℝ) := by simp
    _ = (L.card - (L.filter (fun l => ¬(IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))).card) *
      n^(1/2 - ST_prime_field_eps β) := by
      simp [-not_le, L₁]
      left
      apply eq_sub_of_add_eq
      norm_cast
      apply filter_card_add_filter_neg_card_eq_card
    _ ≥ (L.card - n^(1 - 2*ST_prime_field_eps β) * (Real.sqrt 2 / 4)) * n^(1/2 - ST_prime_field_eps β) := by
      gcongr
      calc ((L.filter (fun l => ¬(IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))).card : ℝ)
        _ = ∑ x in (L.filter (fun l => ¬(IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))), 1 := by simp
        _ ≤ ∑ x in (L.filter (fun l => ¬(IntersectionsP P l).card ≤ (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ))),
          (IntersectionsP P x).card / (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ) := by
          gcongr
          rw [one_le_div]
          apply le_of_lt
          simp_all
          simp
          apply rpow_pos_of_pos
          simp
        _ ≤ (∑ x in L, (IntersectionsP P x).card) / (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ) := by
          simp [sum_div]
          apply sum_le_sum_of_subset_of_nonneg
          simp
          intros
          apply div_nonneg
          simp
          simp
          apply rpow_nonneg
          simp
        _ = (Intersections P L).card / (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ) := by congr 1; norm_cast; rw [IntersectionsP_sum]
        _ ≤ Real.sqrt (L.card * P.card * (L.card + P.card)) / (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ) := by
          gcongr
          rw [le_sqrt]
          norm_cast
          simp
          norm_cast
          simp
        _ ≤ Real.sqrt (n * n * (n+n)) / (4 * n^(1/2 + 2*ST_prime_field_eps β) : ℝ) := by
          gcongr
          apply sqrt_le_sqrt
          gcongr
        _ = n^(1 - 2*ST_prime_field_eps β) * (Real.sqrt 2 / 4) := by
          simp [←mul_two, sqrt_eq_rpow]
          ring_nf
          rw [mul_rpow, ←rpow_nat_cast, ←rpow_mul, ←rpow_neg]
          ring_nf
          conv =>
            lhs
            lhs
            rw [mul_comm, ←mul_assoc, ←rpow_add]
            · skip
            · tactic => simp
          ring_nf
          repeat simp
    _ > (n^(1 - 2*ST_prime_field_eps β) * (ST_C₂^2 / 2)  - n^(1 - 2*ST_prime_field_eps β) * (Real.sqrt 2 / 4)) * n^(1/2 - ST_prime_field_eps β) := by
      gcongr
      rw [←gt_iff_lt]
      calc
        (L.card : ℝ) = L.card * n * (n + n) / (2*n*n) := by ring_nf; simp [mul_comm]
        _ ≥ L.card * P.card * (L.card + P.card) / (2*n*n) := by gcongr
        _ ≥ (Intersections P L).card^2 / (2 * n * n) := by gcongr; norm_cast
        _ > (ST_C₂ * n ^ (3/2 - ST_prime_field_eps β))^2 / (2 * n * n) := by gcongr
        _ = n^(1 - 2*ST_prime_field_eps β) * (ST_C₂^2 / 2) := by
          rw [←rpow_nat_cast, mul_rpow, ←rpow_mul]
          ring_nf
          rw [inv_pow, ←rpow_nat_cast, ←rpow_neg]
          conv =>
            lhs
            lhs
            rw [mul_assoc]
            rhs
            rw [←rpow_add]
            · simp
            · tactic => simp
          norm_num
          ring_nf
          simp
          simp
          simp
          apply rpow_nonneg
          simp
    _ = ((ST_C₂^2 / 2) - Real.sqrt 2 / 4) * (n^(1 - 2*ST_prime_field_eps β) * n^(1/2 - ST_prime_field_eps β)) := by
      ring
    _ = ((ST_C₂^2 / 2) - Real.sqrt 2 / 4) * n^(3/2 - 3*ST_prime_field_eps β) := by
      congr
      rw [←rpow_add]
      congr 1
      ring
      simp
    _ = ST_C₃ * n^(3/2 - ST_prime_field_eps₂ β) := by
      congr 2
      simp only [ST_C₂]
      norm_cast
      rw [NNReal.sq_sqrt]
      simp
      ring_nf
      simp [ST_prime_field_eps]
      ring
  simp_all

theorem ST_prime_field (β : ℝ) (h : 0 < β) (P : Finset (α × α)) (L : Finset (Line α)) (n : ℕ+)
  (nhₗ : (p^β : ℝ) ≤ n) (nhᵤ : n ≤ (p^(2 - β) : ℝ)) (h₁ : P.card ≤ n) (h₂ : L.card ≤ n) :
  (Intersections P L).card ≤ (ST_C * n ^ (3/2 - ST_prime_field_eps β) : ℝ) := by
  calc
    ((Intersections P L).card : ℝ) = ∑ y in L, (IntersectionsP P y).card := by norm_cast; apply IntersectionsP_sum
    _ = ∑ y in L.filter
          (fun y => (IntersectionsP P y).card ≤ (n^(1/2 - ST_prime_field_eps β) : ℝ)), (IntersectionsP P y).card +
        ∑ y in L.filter
          (fun y => ¬(IntersectionsP P y).card ≤ (n^(1/2 - ST_prime_field_eps β) : ℝ)), (IntersectionsP P y).card := by
      norm_cast
      rw [sum_filter_add_sum_filter_not]
    _ ≤ ∑ __ in L.filter
          (fun y => (IntersectionsP P y).card ≤ (n^(1/2 - ST_prime_field_eps β) : ℝ)), (n^(1/2 - ST_prime_field_eps β) : ℝ) +
        ∑ y in L.filter
          (fun y => ¬(IntersectionsP P y).card ≤ (n^(1/2 - ST_prime_field_eps β) : ℝ)), (IntersectionsP P y).card := by
      simp [-sum_const]
      gcongr with i ih
      simp_all
    _ ≤ n^(1/2 - ST_prime_field_eps β) * n +
      ∑ y in L.filter
        (fun y => ¬(IntersectionsP P y).card ≤ (n^(1/2 - ST_prime_field_eps β) : ℝ)), (IntersectionsP P y).card := by
      gcongr ?_ + ?_
      simp
      rw [mul_comm]
      gcongr
      calc (L.filter (fun y => (IntersectionsP P y).card ≤ (n^(2⁻¹ - ST_prime_field_eps β) : ℝ))).card
        _ ≤ L.card := by apply Finset.card_le_card; simp
        _ ≤ n := h₂
      simp
    _ = n^(3/2 - ST_prime_field_eps β) +
        (Intersections P (L.filter (fun y => ¬(IntersectionsP P y).card ≤ (n^(1/2 - ST_prime_field_eps β) : ℝ)))).card := by
      congr
      rw [←rpow_add_one]
      congr 1
      ring
      simp
      rw [IntersectionsP_sum]
    _ ≤ n^(3/2 - ST_prime_field_eps β) + ST_C₂ * n ^ (3/2 - ST_prime_field_eps β) := by
      gcongr
      apply ST_prime_field_aux' <;> try assumption
      calc (L.filter (fun y => ¬(IntersectionsP P y).card ≤ (n^(1/2 - ST_prime_field_eps β) : ℝ))).card
        _ ≤ L.card := by apply Finset.card_le_card; simp
        _ ≤ n := h₂
      intros a b
      simp_all
      linarith
    _ = ST_C * n ^ (3/2 - ST_prime_field_eps β) := by simp [ST_C]; ring
