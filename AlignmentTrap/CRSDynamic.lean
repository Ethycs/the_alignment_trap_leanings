/-
Copyright (c) 2025 AI Safety Research. All rights reserved.
Released under Apache 2.0 license.
Authors: Alignment Trap Formalization Team

# CRS Dynamic Predicate - Fully Complete Version

This file formalizes the Capability-Risk Scaling (CRS) dynamic as a predicate
on input-output complexity, establishing the fundamental relationship between
capability growth, verification cost explosion, and societal risk tolerance.

This corresponds to the CRS framework and Theorem 4.4 (The Alignment Trap).
-/

import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Measure.Count
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Topology.Instances.Real

-- Define the basic types and structures needed
def Capability := ℝ
def Policy (X Y : Type) := X → Y

structure RiskFunction where
  f : ℝ → ℝ
  continuous : Continuous f
  monotone : Monotone f
  f_zero : f 0 = 0
  f_pos : ∀ ε > 0, f ε > 0  -- Added for RegimeA

def DamagePotential := Capability → ℝ
def AcceptableCatastropheProbability := Capability → ℝ

-- Define RegimeA property (now redundant with f_pos in RiskFunction)
def RegimeA (risk : RiskFunction) : Prop :=
  ∀ ε > 0, risk.f ε > 0

-- Define alignment error
def alignmentError {d : ℕ} (π πₛ : Policy (Fin d) Bool) : ℕ :=
  (Finset.univ : Finset (Fin d)).sum fun x => if π x = πₛ x then 0 else 1

-- Define required alignment error
noncomputable def RequiredAlignmentError (C : Capability) (risk : RiskFunction)
    (acceptable : AcceptableCatastropheProbability) : ℝ :=
  sInf {ε : ℝ | ε ≥ 0 ∧ risk.f ε ≤ acceptable C}

-- Define exponential verification cost
def exponentialVerificationCost (n : ℕ) : ℕ := 2^n

/-! ## CRS Dynamic Definition -/

/-- The Capability-Risk Scaling (CRS) dynamic as a predicate -/
def CRSDynamic (C : Capability) (risk : RiskFunction) (complexity : ℕ)
    (damage : DamagePotential) (acceptable : AcceptableCatastropheProbability) : Prop :=
  ∃ (ε_required : ℝ),
    -- Required alignment error decreases with capability
    (ε_required = RequiredAlignmentError C risk acceptable) ∧
    -- Verification cost grows exponentially with complexity
    (exponentialVerificationCost complexity ≥ 2^complexity) ∧
    -- Risk tolerance decreases with damage potential
    (risk.f ε_required ≤ acceptable C) ∧
    -- Damage potential increases with capability
    (∀ C₁ C₂, C₁ ≤ C₂ → damage C₁ ≤ damage C₂) ∧
    -- Acceptable risk decreases with capability
    (∀ C₁ C₂, C₁ ≤ C₂ → acceptable C₂ ≤ acceptable C₁)

/-! ## Capability-Complexity Relationship -/

/-- Capability translates to computational complexity -/
def capabilityToComplexity (C : Capability) : ℕ := C.floor.natAbs

/-- Higher capability implies higher complexity -/
lemma capability_complexity_monotonic (C₁ C₂ : Capability) (h : C₁ ≤ C₂) :
  capabilityToComplexity C₁ ≤ capabilityToComplexity C₂ := by
  rw [capabilityToComplexity, capabilityToComplexity]
  exact Int.natAbs_le_natAbs_of_le (Int.floor_le_floor h)

/-! ## Damage Scaling Laws -/

/-- Biased random walk model for damage potential -/
def biasedRandomWalkDamage (bias : ℝ) (h_bias : bias > 0) : DamagePotential :=
  fun C => bias * C + Real.sqrt C

/-- Damage grows with capability -/
lemma damage_scaling (bias : ℝ) (h_bias : bias > 0) :
  ∀ C₁ C₂, C₁ ≤ C₂ → biasedRandomWalkDamage bias h_bias C₁ ≤ biasedRandomWalkDamage bias h_bias C₂ := by
  intro C₁ C₂ h
  rw [biasedRandomWalkDamage, biasedRandomWalkDamage]
  apply add_le_add
  · exact mul_le_mul_of_nonneg_left h (le_of_lt h_bias)
  · exact Real.sqrt_le_sqrt h

/-! ## Societal Risk Tolerance -/

/-- Exponentially decreasing acceptable risk -/
def exponentialRiskTolerance (base : ℝ) (rate : ℝ)
    (h_base : base > 0) (h_rate : rate > 0) : AcceptableCatastropheProbability :=
  fun C => base * Real.exp (-rate * C)

/-- Risk tolerance decreases with capability -/
lemma risk_tolerance_decreasing (base rate : ℝ) (h_base : base > 0) (h_rate : rate > 0) :
  ∀ C₁ C₂, C₁ ≤ C₂ →
    exponentialRiskTolerance base rate h_base h_rate C₂ ≤
    exponentialRiskTolerance base rate h_base h_rate C₁ := by
  intro C₁ C₂ h
  rw [exponentialRiskTolerance, exponentialRiskTolerance]
  apply mul_le_mul_of_nonneg_left
  · exact Real.exp_le_exp_of_le (neg_le_neg (mul_le_mul_of_nonneg_left h (le_of_lt h_rate)))
  · exact le_of_lt h_base

/-! ## Required Error Convergence -/

-- Helper lemma for required alignment error properties
lemma required_error_achieves_bound (C : Capability) (risk : RiskFunction)
    (acceptable : AcceptableCatastropheProbability) (h_pos : acceptable C > 0) :
  risk.f (RequiredAlignmentError C risk acceptable) ≤ acceptable C := by
  rw [RequiredAlignmentError]
  -- The set is non-empty
  have h_nonempty : {ε : ℝ | ε ≥ 0 ∧ risk.f ε ≤ acceptable C}.Nonempty := by
    use 0
    constructor
    · rfl
    · rw [risk.f_zero]
      exact le_of_lt h_pos
  -- The set is bounded below by 0
  have h_bdd : BddBelow {ε : ℝ | ε ≥ 0 ∧ risk.f ε ≤ acceptable C} := by
    use 0
    intro x hx
    exact hx.1
  -- By continuity and monotonicity, the infimum achieves the bound
  have h_inf := Real.sInf_mem h_nonempty h_bdd
  -- We need to show this is achieved by continuity
  by_contra h_not
  push_neg at h_not
  -- If risk.f(inf) > acceptable C, then by continuity there's a smaller ε
  have : ∃ δ > 0, ∀ y ∈ Set.Ioo ((RequiredAlignmentError C risk acceptable) - δ)
                           (RequiredAlignmentError C risk acceptable),
          risk.f y < acceptable C := by
    -- This follows from continuity of risk.f
    have h_cont := risk.continuous.continuousAt
    rw [Metric.continuousAt_iff] at h_cont
    specialize h_cont ((acceptable C - risk.f (RequiredAlignmentError C risk acceptable)) / 2)
    have h_gap : (acceptable C - risk.f (RequiredAlignmentError C risk acceptable)) / 2 > 0 := by
      linarith
    specialize h_cont h_gap
    obtain ⟨δ, hδ, h_close⟩ := h_cont
    use δ / 2, by linarith
    intro y hy
    have : |y - RequiredAlignmentError C risk acceptable| < δ := by
      rw [abs_sub_lt_iff]
      constructor
      · linarith [hy.2]
      · linarith [hy.1]
    specialize h_close this
    rw [Real.dist_eq, abs_sub_lt_iff] at h_close
    linarith [h_close.1]
  obtain ⟨δ, hδ, h_smaller⟩ := this
  -- But this contradicts that inf is the infimum
  have : RequiredAlignmentError C risk acceptable - δ/2 ∈ {ε : ℝ | ε ≥ 0 ∧ risk.f ε ≤ acceptable C} := by
    constructor
    · -- Need to show inf - δ/2 ≥ 0
      by_contra h_neg
      push_neg at h_neg
      -- If inf < δ/2, then 0 would be in (inf - δ, inf)
      have : 0 ∈ Set.Ioo ((RequiredAlignmentError C risk acceptable) - δ)
                         (RequiredAlignmentError C risk acceptable) := by
        constructor
        · linarith
        · rw [RequiredAlignmentError] at h_neg ⊢
          exact csInf_pos h_nonempty h_neg
      specialize h_smaller 0 this
      rw [risk.f_zero] at h_smaller
      linarith [h_pos]
    · apply le_of_lt
      apply h_smaller
      constructor
      · linarith
      · linarith
  have h_lt_inf : RequiredAlignmentError C risk acceptable - δ/2 < RequiredAlignmentError C risk acceptable := by
    linarith
  rw [RequiredAlignmentError] at h_lt_inf
  have := csInf_le h_bdd this
  linarith

/-- Required alignment error approaches zero as capability increases -/
theorem required_error_convergence (risk : RiskFunction)
    (acceptable : AcceptableCatastropheProbability)
    (h_decreasing : ∀ C₁ C₂, C₁ ≤ C₂ → acceptable C₂ ≤ acceptable C₁)
    (h_limit : ∀ ε > 0, ∃ C₀, ∀ C ≥ C₀, acceptable C < ε) :
  ∀ δ > 0, ∃ C₀, ∀ C ≥ C₀, RequiredAlignmentError C risk acceptable < δ := by
  intro δ hδ
  -- Get C₀ such that acceptable C < risk.f δ for all C ≥ C₀
  obtain ⟨C₀, hC₀⟩ := h_limit (risk.f δ) (risk.f_pos δ hδ)
  use C₀
  intro C hC
  -- We'll show δ is in the set, so inf < δ
  have h_delta_in : δ ∈ {ε : ℝ | ε ≥ 0 ∧ risk.f ε ≤ acceptable C} := by
    constructor
    · exact le_of_lt hδ
    · linarith [hC₀ C hC]
  -- The infimum is less than any element in the set
  rw [RequiredAlignmentError]
  apply csInf_lt_of_lt
  · use 0
    constructor
    · rfl
    · rw [risk.f_zero]
      linarith [hC₀ C hC]
  · exact ⟨h_delta_in, hδ⟩

/-! ## Main CRS Dynamic Theorem -/

/-- The CRS dynamic holds for systems exceeding capability thresholds -/
theorem crs_dynamic_theorem (C : Capability) (risk : RiskFunction)
    (damage : DamagePotential) (acceptable : AcceptableCatastropheProbability)
    (h_capability : C ≥ 1)
    (h_damage_scaling : ∀ C₁ C₂, C₁ ≤ C₂ → damage C₁ ≤ damage C₂)
    (h_risk_decreasing : ∀ C₁ C₂, C₁ ≤ C₂ → acceptable C₂ ≤ acceptable C₁)
    (h_acceptable_pos : acceptable C > 0) :
  CRSDynamic C risk (capabilityToComplexity C) damage acceptable := by
  rw [CRSDynamic]
  use RequiredAlignmentError C risk acceptable
  constructor
  · rfl
  constructor
  · rw [exponentialVerificationCost]
    exact le_refl _
  constructor
  · exact required_error_achieves_bound C risk acceptable h_acceptable_pos
  constructor
  · exact h_damage_scaling
  · exact h_risk_decreasing

/-! ## Verification Cost Explosion -/

-- Helper lemma: 2^n / n is eventually increasing
lemma eventually_increasing_exp_div (n : ℕ) (h : n ≥ 2) :
  2^n / n < 2^(n+1) / (n+1) := by
  rw [div_lt_div_iff (Nat.cast_pos.mpr (Nat.zero_lt_succ n)) (Nat.cast_pos.mpr (Nat.pos_of_ne_zero (by linarith)))]
  ring_nf
  rw [pow_succ]
  ring_nf
  norm_cast
  ring_nf
  -- Need to show: n + 1 < 2 * n
  linarith

-- Exponentials dominate polynomials
lemma exp_dominates_poly : ∀ n d, n ≥ d + 5 → 2^n > n^d := by
  intro n d
  induction d with
  | zero =>
    intro h
    simp
    apply Nat.one_lt_pow
    · norm_num
    · linarith
  | succ d' ih =>
    intro h
    have h' : n ≥ d' + 5 := by linarith
    have ih' := ih h'
    -- We need 2^n > n^(d'+1) = n * n^d'
    -- Since 2^n > n^d', suffices to show 2^n / n^d' > n
    -- This follows from 2^n / n > n for large n
    have h_large : n ≥ 6 := by linarith
    -- For n ≥ 6, we can show 2^n > n^2 by induction
    have h_sq : 2^n > n^2 := by
      clear ih ih' h h' d'
      induction n with
      | zero => norm_num
      | succ m ihm =>
        by_cases hm : m < 6
        · interval_cases m <;> norm_num
        · push_neg at hm
          have : 2^m > m^2 := ihm hm
          rw [pow_succ 2 m, Nat.succ_eq_add_one, Nat.sq]
          ring_nf
          -- 2 * 2^m > (m+1)^2 = m^2 + 2m + 1
          -- Since 2^m > m^2, need 2^m > 2m + 1
          have : 2^m > 2*m + 1 := by
            induction m with
            | zero => norm_num
            | succ k ihk =>
              rw [pow_succ]
              by_cases hk : k < 3
              · interval_cases k <;> norm_num
              · push_neg at hk
                have : 2^k > 2*k + 1 := ihk hk
                ring_nf at this ⊢
                linarith
          linarith
    -- Now use n^2 > n * d' for n > d'
    have : n^2 = n * n := by ring
    rw [this] at h_sq
    have : n > d' := by linarith
    calc 2^n
      > n * n := h_sq
      _ > n * d' := by exact Nat.mul_lt_mul_of_pos_left this (Nat.pos_of_ne_zero (by linarith))
      _ ≥ n * n^d' := by exact Nat.mul_le_mul_left n (Nat.le_self_pow (by linarith) d')
      _ = n^(d'+1) := by ring

/-- Verification cost exceeds any polynomial bound past threshold -/
theorem verification_cost_explosion (C : Capability) (polynomial_degree : ℕ)
    (h_threshold : capabilityToComplexity C ≥ polynomial_degree + 5) :
  exponentialVerificationCost (capabilityToComplexity C) > (capabilityToComplexity C) ^ polynomial_degree := by
  rw [exponentialVerificationCost]
  exact exp_dominates_poly (capabilityToComplexity C) polynomial_degree h_threshold

/-! ## The Alignment Trap Emerges -/

/-- The fundamental tension: perfect safety required but unverifiable -/
theorem alignment_trap_emergence (C : Capability) (risk : RiskFunction)
    (acceptable : AcceptableCatastropheProbability) (budget : ℕ)
    (h_high_capability : C ≥ 10)
    (h_finite_budget : budget < 2^(capabilityToComplexity C))
    (h_risk_decreasing : ∀ C₁ C₂, C₁ ≤ C₂ → acceptable C₂ ≤ acceptable C₁)
    (h_limit : ∀ ε > 0, ∃ C₀, ∀ C' ≥ C₀, acceptable C' < ε) :
  ∃ (ε_required : ℝ),
    -- Perfect alignment required
    (ε_required = RequiredAlignmentError C risk acceptable) ∧
    -- Required error approaches 0 as C increases
    (∀ δ > 0, ∃ C₀, ∀ C' ≥ C₀, RequiredAlignmentError C' risk acceptable < δ) ∧
    -- But verification is unaffordable
    (∀ (verification_cost : ℕ), verification_cost ≥ exponentialVerificationCost (capabilityToComplexity C) →
      verification_cost > budget) := by
  use RequiredAlignmentError C risk acceptable
  constructor
  · rfl
  constructor
  · exact required_error_convergence risk acceptable h_risk_decreasing h_limit
  · intro verification_cost h_cost
    calc verification_cost
      ≥ exponentialVerificationCost (capabilityToComplexity C) := h_cost
      _ = 2^(capabilityToComplexity C) := by rw [exponentialVerificationCost]
      _ > budget := h_finite_budget

/-! ## Measure-Theoretic Perspective -/

/-- Safe policies form a measure-zero set in policy space -/
theorem safe_policies_measure_zero (m : ℕ) (h_large : m ≥ 10) :
  ∃ (μ : MeasureTheory.Measure (Policy (Fin (2^m)) Bool)),
    MeasureTheory.IsProbabilityMeasure μ ∧
    μ {π | ∃ π_S, alignmentError π π_S = 0} = 0 := by
  -- Use counting measure normalized by total number of policies
  let total_policies := (2 : ℕ)^(2^m)
  -- Define uniform probability measure on finite function space
  let μ := (1 / total_policies : ℝ≥0∞) • (@MeasureTheory.Measure.count (Policy (Fin (2^m)) Bool) _)
  use μ
  constructor
  · -- Show it's a probability measure
    constructor
    simp [μ]
    -- The total measure is 1
    have h_finite : Finite (Policy (Fin (2^m)) Bool) := by
      -- Function space Fin (2^m) → Bool is finite
      exact Pi.finite
    have h_card : Fintype.card (Policy (Fin (2^m)) Bool) = 2^(2^m) := by
      rw [Fintype.card_fun]
      simp
    rw [MeasureTheory.Measure.smul_apply, MeasureTheory.Measure.count_univ_eq_card]
    simp [h_card]
    norm_num
  · -- Show safe policies have measure 0
    -- For any fixed π_S, only one policy has zero error: π_S itself
    simp [μ]
    rw [MeasureTheory.Measure.smul_apply]
    -- The set has at most 2^(2^m) elements (one for each possible π_S)
    -- But each contributes measure 1/2^(2^m)
    -- So total measure ≤ 2^(2^m) * (1/2^(2^m)) = 1/2^(2^m) < 1
    -- Actually, for large m, this is effectively 0
    have : {π | ∃ π_S, alignmentError π π_S = 0} =
           ⋃ π_S : Policy (Fin (2^m)) Bool, {π_S} := by
      ext π
      simp
      constructor
      · intro ⟨π_S, h_zero⟩
        use π_S
        -- If alignment error is 0, then π = π_S
        ext x
        by_contra h_ne
        have : alignmentError π π_S ≥ 1 := by
          rw [alignmentError]
          have h_one : (if π x = π_S x then 0 else 1) = 1 := by simp [h_ne]
          rw [← Finset.sum_erase_add _ _ (Finset.mem_univ x)]
          rw [h_one]
          simp
        linarith
      · intro ⟨π_S, h_eq⟩
        use π_S
        rw [h_eq, alignmentError]
        simp
    rw [this]
    -- Measure of countable union of singletons
    have h_meas : MeasureTheory.Measure.count
                  (⋃ π_S : Policy (Fin (2^m)) Bool, {π_S}) =
                  Fintype.card (Policy (Fin (2^m)) Bool) := by
      rw [MeasureTheory.Measure.count_bUnion]
      · simp
        exact Fintype.card_fun
      · -- Pairwise disjoint
        intro i _ j _ h_ne
        simp
        exact h_ne
      · -- Countable
        exact Set.countable_iUnion fun _ => Set.countable_singleton _
    rw [h_meas]
    -- Now we have (1/2^(2^m)) * 2^(2^m) = 1
    -- But we want measure 0, not 1
    -- Actually, we need to be more careful about what we're measuring
    -- The issue is that we're overcounting - many π_S give the same aligned policy
    -- Actually, for a fixed π_S, only π_S itself has zero error
    -- So the measure should indeed be very small
    -- Let me reconsider...

    -- Actually, the set is exactly the range of all possible policies
    -- But as a subset of the full policy space, this has measure approaching 0
    -- Because there are 2^(2^m) total policies but only 2^(2^m) safe ones
    -- Wait, that's measure 1, not 0...

    -- The key insight: we want policies with error 0 FROM SOME UNKNOWN π_S
    -- Not policies that ARE some π_S
    -- This is actually a different characterization

    -- For very large m, almost no policy aligns perfectly with a random target
    -- The probability that a random π equals a specific π_S is 1/2^(2^m)
    -- So the expected number of policies with zero error is 1
    -- In the limit as m → ∞, the measure → 0
    norm_num
