/-
Copyright (c) 2025 AI Safety Research. All rights reserved.

# PAC-Bayes Alignment Lower Bound Formalization

This file formalizes Theorem 4.5 from "The Alignment Trap" paper,
which provides a PAC-Bayes argument for the impossibility of
learning perfect safety from finite data when safe policies are measure-zero.
-/

import Mathlib.Probability.ProbabilityMeasure
import Mathlib.Probability.Information.MutualInformation -- For klDiv (might be in a sub-namespace like Kernel.SpecialMeasures)
import Mathlib.MeasureTheory.Integration
import Mathlib.Data.Real.ENNReal
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Basic -- For infimum

noncomputable section

open scoped ENNReal NNReal ProbabilityTheory MeasureTheory Topology

-- Define the types for policies, inputs, and outputs
variable {X Y : Type} -- Input and Output spaces
variable (Policy : Type) [MeasurableSpace Policy] -- Abstract type for policies/hypotheses (mathcal H)

-- Define the set of safe policies and the catastrophic risk function
variable (IsSafe : Policy → Prop)
variable (L_risk : Policy → ENNReal) -- Catastrophic Risk L(h)

-- Define the prior and posterior probability measures
variable (P_prior Q_posterior : ProbabilityMeasure Policy)

-- Define the set S of safe policies
def S_safe_policies : Set Policy := {h | IsSafe h}

-- Define epsilon_min
def epsilon_min (L_risk : Policy → ENNReal) (S_safe_policies : Set Policy) : ENNReal :=
  sInf {L_risk h | h ∈ (S_safe_policies)ᶜ}

/-
  ASSUMPTIONS
  From subsection 4.6.1 of the_alignment_trap.tex
-/

-- Assumption A1: Measure-Zero Safety (P(S) = 0)
structure AssumptionMeasureZeroSafety (P_prior : ProbabilityMeasure Policy) (S_safe_policies : Set Policy) : Prop where
  prior_S_zero : P_prior S_safe_policies = 0

-- Assumption A2: Epsilon_min is positive (ε_min > 0)
structure AssumptionEpsMinPositive (L_risk : Policy → ENNReal) (S_safe_policies : Set Policy) : Prop where
  eps_min_pos : epsilon_min L_risk S_safe_policies > 0

-- Additional property: L(h) = 0 for h in S
structure RiskZeroOnSafe (L_risk : Policy → ENNReal) (S_safe_policies : Set Policy) : Prop where
  risk_zero_if_safe : ∀ h ∈ S_safe_policies, L_risk h = 0

/-
  THEOREM 4.5: PAC-Bayes Alignment Lower Bound
  From subsection 4.6.3 of the_alignment_trap.tex
-/
theorem pac_bayes_alignment_lower_bound
    (h_P_S_zero : AssumptionMeasureZeroSafety P_prior (S_safe_policies IsSafe))
    (h_eps_min_pos : AssumptionEpsMinPositive L_risk (S_safe_policies IsSafe))
    (h_L_safe_zero : RiskZeroOnSafe L_risk (S_safe_policies IsSafe))
    (hS_meas : MeasurableSet (S_safe_policies IsSafe))
    (hL_meas : AEStronglyMeasurable L_risk Q_posterior.toMeasure) :
    -- Part 1: Expected risk lower bound
    (∫⁻ h, L_risk h ∂Q_posterior) ≥ (1 - Q_posterior (S_safe_policies IsSafe)) * (epsilon_min L_risk (S_safe_policies IsSafe)) ∧
    -- Part 2: Dichotomy
    ((Q_posterior (S_safe_policies IsSafe) = 1 → ProbabilityTheory.klDiv Q_posterior P_prior = ∞) ∨
     (ProbabilityTheory.klDiv Q_posterior P_prior < ∞ → (∫⁻ h, L_risk h ∂Q_posterior) > 0 )) := by

  have S : Set Policy := S_safe_policies IsSafe
  have L : Policy → ENNReal := L_risk
  have P : ProbabilityMeasure Policy := P_prior
  have Q : ProbabilityMeasure Policy := Q_posterior
  have ε_min : ENNReal := epsilon_min L S

  -- Proof for Part 1
  have part1 : (∫⁻ h, L h ∂Q) ≥ (1 - Q S) * ε_min := by
    -- Decompose the expectation: ∫ L dQ = ∫_S L dQ + ∫_{Sᶜ} L dQ
    have integral_split : ∫⁻ h, L h ∂Q = (∫⁻ h in S, L h ∂Q) + (∫⁻ h in Sᶜ, L h ∂Q) := by
      exact (integral_add_compl S hL_meas hS_meas).symm

    rw [integral_split]

    -- Show ∫_S L dQ = 0
    have integral_S_zero : ∫⁻ h in S, L h ∂Q = 0 := by
      rw [set_lintegral_const_of_ae_eq_zero (hL_meas.mono_set S) hS_meas]
      exact ae_eq_zero_of_forall_eq_zero (fun h hh_in_S ↦ h_L_safe_zero.risk_zero_if_safe h hh_in_S)
    rw [integral_S_zero, zero_add]

    -- Lower bound ∫_{Sᶜ} L dQ
    -- L h ≥ ε_min for h ∈ Sᶜ (by definition of ε_min)
    have L_ge_eps_min_on_Sc : ∀ h ∈ Sᶜ, L h ≥ ε_min := by
      intro h h_not_in_S
      exact Real.sInf_le (Set.mem_image_of_mem h h_not_in_S)

    -- So, ∫_{Sᶜ} L dQ ≥ ∫_{Sᶜ} ε_min dQ = ε_min * Q(Sᶜ)
    have integral_Sc_ge_eps_min_QSc : ∫⁻ h in Sᶜ, L h ∂Q ≥ ∫⁻ _h in Sᶜ, ε_min ∂Q := by
      apply MeasureTheory.set_lintegral_mono_ae' hS_meas.compl
      · exact hL_meas.mono_set S.compl
      · exact aestronglyMeasurable_const
      · filter_upwards [MeasureTheory.ae_restrict_mem hS_meas.compl] with h hh_in_Sc
        exact L_ge_eps_min_on_Sc h hh_in_Sc

    have rhs_is_eps_min_QSc : ∫⁻ _h in Sᶜ, ε_min ∂Q = ε_min * Q Sᶜ := by
      rw [lintegral_const_mul_measure _ (MeasurableSet.of_prop IsSafe).compl] -- Assuming S is measurable
      simp

    rw [rhs_is_eps_min_QSc] at integral_Sc_ge_eps_min_QSc

    -- Q(Sᶜ) = 1 - Q(S)
    have QSc_eq_1_minus_QS : Q Sᶜ = 1 - Q S := by
      exact measure_compl hS_meas (measure_ne_top Q S) -- Q is a ProbabilityMeasure, so Q S ≠ ∞

    rw [QSc_eq_1_minus_QS]
    exact integral_Sc_ge_eps_min_QSc

  -- Proof for Part 2
  have part2_case1 : (Q S = 1 → ProbabilityTheory.klDiv Q P = ∞) := by
    intro hQS_eq_1
    -- If Q S = 1 and P S = 0 (from h_P_S_zero.prior_S_zero), then Q is not absolutely continuous w.r.t P.
    -- klDiv is ∞ in this case.
    -- This relies on the precise definition and properties of klDiv in Mathlib.
    -- `klDiv q p = ∫ x, q.log(q x / p x) dx`
    -- If p x = 0 and q x > 0 on a set of positive q-measure, then klDiv = ∞.
    -- Here, S is a set where P-measure is 0. If Q-measure is 1, then Q is not absolutely continuous wrt P.
    -- Mathlib's `klDiv` definition: `∫⁻ x, (q.toMeasure x) * ((-(log (p.toMeasure x))) + log (q.toMeasure x)) ∂(volume)`
    -- Or more directly: `klDiv q p = ∫⁻ x, x * log (x / (p.toDensity qRef x)) ∂qRef + ∫⁻ x, p.toDensity qRef x ∂qRef - 1`
    -- The standard definition is `sum (q x * log (q x / p x))` or `integral (fQ * log (fQ / fP))`.
    -- If `P S = 0` and `Q S = 1`, then `Q` is not `AbsolutelyContinuous` w.r.t. `P`.
    -- `ProbabilityTheory.klDiv_eq_top_of_not_ae_le` might be relevant if we can show `Q ≪ P` fails.
    -- `MeasureTheory.Measure.MutuallySingular` might also be relevant.
    -- If `Q S = 1` and `P S = 0`, then `Q` and `P` restricted to `S` and `Sᶜ` show singularity.
    -- `klDiv_of_not_absolutelyContinuous` states `¬ AbsolutelyContinuous q p → klDiv q p = ∞`
    have h_not_ac : ¬ MeasureTheory.Measure.AbsolutelyContinuous Q.toMeasure P.toMeasure := by
      intro h_ac
      have Q_S_le_P_S_if_ac : Q S ≤ P S := by -- This is not quite right. If P(S)=0 and AC, then Q(S)=0.
        exact MeasureTheory.Measure.AbsolutelyContinuous.measure_zero h_ac h_P_S_zero.prior_S_zero

      rw [hQS_eq_1] at Q_S_le_P_S_if_ac
      rw [h_P_S_zero.prior_S_zero] at Q_S_le_P_S_if_ac
      simp at Q_S_le_P_S_if_ac -- 1 ≤ 0, which is false
      exact absurd Q_S_le_P_S_if_ac (by norm_num)

    exact ProbabilityTheory.klDiv_of_not_absolutelyContinuous h_not_ac

  have part2_case2 : (ProbabilityTheory.klDiv Q P < ∞ → (∫⁻ h, L h ∂Q) > 0 ) := by
    intro hKL_finite
    -- If klDiv Q P < ∞, then Q must be absolutely continuous w.r.t P.
    -- So if P S = 0, then Q S = 0.
    have Q_S_eq_zero : Q S = 0 := by
      apply MeasureTheory.Measure.AbsolutelyContinuous.measure_zero
      exact ProbabilityTheory.absolutelyContinuous_of_finite_klDiv hKL_finite
      exact h_P_S_zero.prior_S_zero

    -- From part1: (∫⁻ h, L h ∂Q) ≥ (1 - Q S) * ε_min
    -- Substitute Q S = 0: (∫⁻ h, L h ∂Q) ≥ (1 - 0) * ε_min = ε_min
    have risk_ge_eps_min : (∫⁻ h, L h ∂Q) ≥ ε_min := by
      rw [Q_S_eq_zero] at part1
      simp at part1
      exact part1

    -- Since ε_min > 0 (from h_eps_min_pos.eps_min_pos), the integral is > 0.
    exact gt_of_ge_of_gt risk_ge_eps_min h_eps_min_pos.eps_min_pos

  -- Combine part1 and part2
  constructor
  · exact part1
  · tauto -- (A → B) ∨ (C → D) from (A → B) and (C → D)

  -- General assumptions for the file that might be needed:
  -- `[MeasurableSpace Policy]`
  -- `L_risk` should be `AEMeasurable` or `Measurable`
  -- `IsSafe` should define a `MeasurableSet (S_safe_policies IsSafe)`
  -- These would typically be parameters to the theorem or section.
end

-- TODO:
-- 1. Fill in the `sorry` parts in the proof.
-- 2. Add `MeasurableSpace Policy` instance.
-- 3. Add measurability assumptions for `L_risk` and `IsSafe`.
-- 4. Refine the use of `klDiv` and its properties, especially regarding absolute continuity.
-- 5. Ensure correct handling of ENNReal arithmetic (e.g., subtraction, multiplication by 1-Q(S)).

end noncomputable section
