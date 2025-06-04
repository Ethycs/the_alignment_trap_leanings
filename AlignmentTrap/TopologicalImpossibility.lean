import Mathlib.Topology.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
-- ... (other necessary imports from your original file)
import Mathlib.MeasureTheory.Measure.NullMeasurableSet -- for measure_empty
import Mathlib.MeasureTheory.Integral.SetIntegral -- for set_lintegral_congr_fun
import Mathlib.MeasureTheory.Function.AEEqFun -- for ae_eq_fun
import Mathlib.Data.Set.Pointwise -- for countable_of_isolated_points if needed
import Mathlib.Topology.MetricSpace.isOpen_IsEmpty -- for isOpen_interior

open Metric Topology MeasureTheory Probability Finset Set Real List
open scoped ENNReal NNReal BigOperators ProbabilityTheory

-- Assume definitions: ParameterSpace, SafeSet, SafeBoundary, TrainingPath,
-- IsOnFace, IsOutwardNormalDerivAtFace

-- For simplicity, assume paths are C¹ where needed for derivative arguments.
variable {n : ℕ} [hn_fact : Fact (n ≥ 2)] (ε_global : ℝ) (hε_global_pos : 0 < ε_global)
variable (γ : TrainingPath n) -- TrainingPath is C(ℝ≥0, ParameterSpace n)
variable (hγ_C1 : ∀ t : ℝ≥0, DifferentiableAt ℝ (fun s : ℝ => γ ⟨s, sorry_cast_nonneg⟩) t.val) -- Simplified C1 assumption
variable (hγ_starts_outside : γ 0 ∉ SafeSet n ε_global)

-- Axiom 1: Face Interaction (Strengthened Transversality)
axiom Axiom1_FaceInteraction (γ_path : TrainingPath n) (hγ_path_C1) (hγ_path_starts_outside) :
  ∀ t_nnreal : ℝ≥0, γ_path t_nnreal ∈ SafeBoundary n ε_global →
    ∃ (i : Fin n), IsOnFace γ_path t_nnreal ε_global i ∧ IsOutwardNormalDerivAtFace γ_path t_nnreal ε_global i

-- Axiom 2: No Interior Entry (Given Axiom1 and starts outside, interior is never entered)
axiom Axiom2_NoInteriorEntry (γ_path : TrainingPath n) (hγ_path_C1) (hγ_path_starts_outside)
  (h_ax1_holds_for_γ : -- Explicitly pass that Axiom1 holds for this γ
    ∀ t_nnreal : ℝ≥0, γ_path t_nnreal ∈ SafeBoundary n ε_global →
      ∃ (i : Fin n), IsOnFace γ_path t_nnreal ε_global i ∧ IsOutwardNormalDerivAtFace γ_path t_nnreal ε_global i) :
  {t_val : ℝ | ⟨t_val, sorry_cast_nonneg⟩ ∈ {t' : ℝ≥0 | γ_path t' ∈ interior (SafeSet n ε_global)}} = ∅

-- Axiom 3: Zero Occupation Time on Edges/Corners (Given Axiom1 and starts outside)
axiom Axiom3_ZeroEdgeCornerTime (γ_path : TrainingPath n) (hγ_path_C1) (hγ_path_starts_outside)
  (h_ax1_holds_for_γ : -- Explicitly pass that Axiom1 holds for this γ
    ∀ t_nnreal : ℝ≥0, γ_path t_nnreal ∈ SafeBoundary n ε_global →
      ∃ (i : Fin n), IsOnFace γ_path t_nnreal ε_global i ∧ IsOutwardNormalDerivAtFace γ_path t_nnreal ε_global i) :
  volume {t_val : ℝ | ⟨t_val, sorry_cast_nonneg⟩ ∈
    {t' : ℝ≥0 | γ_path t' ∈ (frontier (SafeSet n ε_global) \ SafeBoundary n ε_global)}} = 0


-- Assume face_exit_immediately_detailed is proven using Axiom1_FaceInteraction
lemma face_exit_immediately_from_Axiom1
  {i : Fin n} {t₀_nnreal : ℝ≥0}
  (h_on_face_i : IsOnFace γ t₀_nnreal ε_global i)
  (h_outward_deriv_i : IsOutwardNormalDerivAtFace γ t₀_nnreal ε_global i) :
  ∃ δ > 0, ∀ t_val : ℝ, t_val ∈ Set.Ioo t₀_nnreal.val (t₀_nnreal.val + δ) →
    γ ⟨t_val, sorry_cast_nonneg⟩ ∉ SafeSet n ε_global :=
begin
  sorry -- Proof uses h_outward_deriv_i which comes from Axiom1
end

-- Lemma: Time spent on SafeBoundary is measure zero (Countability argument)
lemma occupation_time_SafeBoundary_is_zero
  (h_ax1_for_γ : ∀ t_nnreal : ℝ≥0, γ t_nnreal ∈ SafeBoundary n ε_global →
    ∃ (i : Fin n), IsOnFace γ t_nnreal ε_global i ∧ IsOutwardNormalDerivAtFace γ t_nnreal ε_global i)
  {T_val : ℝ} (hT_pos : 0 < T_val) :
  volume {t_val ∈ Ioo 0 T_val | γ ⟨t_val, sorry_cast_nonneg⟩ ∈ SafeBoundary n ε_global} = 0 :=
begin
  let E_boundary_times := {t_val ∈ Ioo 0 T_val | γ ⟨t_val, sorry_cast_nonneg⟩ ∈ SafeBoundary n ε_global},
  have E_boundary_times_countable : E_boundary_times.Countable,
  { apply Set.countable_of_isolated_points,
    intros t_iso_val ht_iso_prop,
    let t_iso_nnreal : ℝ≥0 := ⟨t_iso_val, sorry_cast_nonneg_interval ht_iso_prop.1⟩,
    rcases h_ax1_for_γ t_iso_nnreal ht_iso_prop.2 with ⟨i, h_on_face, h_outward⟩,
    obtain ⟨δ_exit_right, hδ_er_pos, h_exits_right⟩ :=
      face_exit_immediately_from_Axiom1 h_on_face h_outward,
    -- Argument for left-isolation (as sketched before, using C1 and derivative sign)
    obtain ⟨δ_exit_left, hδ_el_pos, h_interior_left⟩ : ∃ δ_l > 0, ∀ s_val ∈ Ioo (t_iso_val - δ_l) t_iso_val,
        γ ⟨s_val, sorry_cast_nonneg⟩ ∈ interior (SafeSet n ε_global) ∨ γ ⟨s_val, sorry_cast_nonneg⟩ ∉ SafeSet n ε_global,
    { sorry_TODO "Left isolation detailed proof from C1 and outward deriv" },

    use min δ_exit_right δ_exit_left, by { refine lt_min hδ_er_pos hδ_el_pos },
    rw Set.eq_singleton_iff_unique_mem,
    split,
    { exact ht_iso_prop, },
    { intros s_val hs_s_in_inter,
      by_cases h_s_eq_t_iso : s_val = t_iso_val, { exact h_s_eq_t_iso },
      { have hs_s_on_boundary := hs_s_in_inter.2,
        cases (lt_or_gt_of_ne h_s_eq_t_iso) with h_s_lt_t_iso h_s_gt_t_iso,
        { -- s_val < t_iso_val
          specialize h_interior_left s_val (sorry_proof_s_in_left_interval hs_s_in_inter.1 (min_le_right _ _)),
          cases h_interior_left with h_s_in_int h_s_not_in_safe,
          { exact (disjoint_interior_frontier (SafeSet n ε_global)).ne_of_mem
              h_s_in_int (mem_frontier_of_mem_safe_boundary hs_s_on_boundary) },
          { exact h_s_not_in_safe (mem_of_mem_safe_boundary hs_s_on_boundary) }
        },
        { -- s_val > t_iso_val
          exact h_exits_right s_val (sorry_proof_s_in_right_interval hs_s_in_inter.1 (min_le_left _ _))
                                (mem_of_mem_safe_boundary hs_s_on_boundary),
        }
      }}
  },
  exact measure_countable_null E_boundary_times_countable,
end


-- The main helper lemma, now relying on the axioms
lemma zero_occupation_time_helper_with_axioms
  (h_ax1_for_γ : ∀ t_nnreal : ℝ≥0, γ t_nnreal ∈ SafeBoundary n ε_global →
    ∃ (i : Fin n), IsOnFace γ t_nnreal ε_global i ∧ IsOutwardNormalDerivAtFace γ t_nnreal ε_global i)
  (h_ax2_for_γ : {t_val : ℝ | ⟨t_val, sorry_cast_nonneg⟩ ∈ {t' : ℝ≥0 | γ t' ∈ interior (SafeSet n ε_global)}} = ∅)
  (h_ax3_for_γ : volume {t_val : ℝ | ⟨t_val, sorry_cast_nonneg⟩ ∈
    {t' : ℝ≥0 | γ t' ∈ (frontier (SafeSet n ε_global) \ SafeBoundary n ε_global)}} = 0)
  {T_val : ℝ} (hT_pos : 0 < T_val) :
  ∫⁻ (t : ℝ) in Ioo 0 T_val, (SafeSet n ε_global).indicator (fun _ => 1 : ℝ≥0∞)
      (γ ⟨t, sorry_cast_nonneg_interval (mem_Ioo.mp ‹_›).1⟩) = 0 :=
begin
  let E_γ_times := {t_val ∈ Ioo 0 T_val | γ ⟨t_val, sorry_cast_nonneg_interval (mem_Ioo.mp ‹_›).1⟩ ∈ SafeSet n ε_global},

  -- Show that E_γ_times has measure zero.
  have h_vol_E_γ_zero : volume E_γ_times = 0,
  { -- If t ∈ E_γ_times, then γ(t) ∈ SafeSet.
    -- By Axiom 2 (h_ax2_for_γ), γ(t) ∉ interior(SafeSet).
    -- So, γ(t) ∈ SafeSet \ interior(SafeSet) = frontier(SafeSet).
    have E_γ_subset_frontier_times : E_γ_times ⊆
      {t_val ∈ Ioo 0 T_val | γ ⟨t_val, sorry_cast_nonneg_interval (mem_Ioo.mp ‹_›).1⟩ ∈ frontier (SafeSet n ε_global)},
    { intros t_v ht_v_in_E_gamma,
      simp only [E_γ_times, mem_setOf_eq] at ht_v_in_E_gamma,
      refine ⟨ht_v_in_E_gamma.1, _⟩,
      have h_gamma_tv_in_safe : γ ⟨t_v, _⟩ ∈ SafeSet n ε_global := ht_v_in_E_gamma.2,
      have h_gamma_tv_not_in_int : γ ⟨t_v, _⟩ ∉ interior (SafeSet n ε_global),
      { intro h_in_int_contra,
        apply Set.not_mem_empty t_v, -- using (h_ax2_for_γ t_v)
        rw ← h_ax2_for_γ,
        simp only [mem_setOf_eq],
        exact ⟨⟨t_v, sorry_cast_nonneg_interval ht_v_in_E_gamma.1⟩ , h_in_int_contra⟩,
      },
      exact mem_frontier_iff_mem_closure_inter_closure_compl.mpr
            ⟨isClosed_SafeSet.closure_eq ▸ h_gamma_tv_in_safe,
             by { rw closure_compl, exact subset_compl_interior _ h_gamma_tv_not_in_int }⟩,
    },

    let E_frontier_times := {t_val ∈ Ioo 0 T_val | γ ⟨t_val, _⟩ ∈ frontier (SafeSet n ε_global)},
    let E_SafeBoundary_times := {t_val ∈ Ioo 0 T_val | γ ⟨t_val, _⟩ ∈ SafeBoundary n ε_global},
    let E_EdgeCorner_times := {t_val ∈ Ioo 0 T_val | γ ⟨t_val, _⟩ ∈ (frontier (SafeSet n ε_global) \ SafeBoundary n ε_global)},

    have h_frontier_decomp : E_frontier_times = E_SafeBoundary_times ∪ E_EdgeCorner_times,
    { ext t_v, split,
      { intro h,
        simp only [E_frontier_times, E_SafeBoundary_times, E_EdgeCorner_times, mem_setOf_eq, mem_union] at *,
        refine ⟨h.1, _⟩, by_cases γ ⟨t_v, _⟩ ∈ SafeBoundary n ε_global; simp [*], },
      { intro h,
        simp only [E_frontier_times, E_SafeBoundary_times, E_EdgeCorner_times, mem_setOf_eq, mem_union] at *,
        exact ⟨h.1, by { cases h.2; simp [*, SafeBoundary_subset_frontier, diff_subset_frontier] }⟩,
      }
    },
    rw h_frontier_decomp,

    have h_vol_SafeBoundary_zero := occupation_time_SafeBoundary_is_zero γ hγ_C1 h_ax1_for_γ hT_pos,

    -- Need to adapt Axiom 3 for the interval Ioo 0 T_val
    have h_vol_EdgeCorner_zero_interval : volume E_EdgeCorner_times = 0,
    { -- Axiom3 is for all time. E_EdgeCorner_times is restricted to Ioo 0 T_val.
      -- volume (A ∩ B) ≤ volume A
      let Full_E_EdgeCorner_times := {t_val : ℝ | ⟨t_val, sorry_cast_nonneg⟩ ∈
        {t' : ℝ≥0 | γ t' ∈ (frontier (SafeSet n ε_global) \ SafeBoundary n ε_global)}},
      have : E_EdgeCorner_times ⊆ Full_E_EdgeCorner_times := by intro t _; simp [E_EdgeCorner_times, Full_E_EdgeCorner_times]; tauto,
      exact measure_mono_null this (Axiom3_ZeroEdgeCornerTime γ hγ_C1 hγ_starts_outside h_ax1_for_γ),
    },

    rw ← measure_union_null_iff E_SafeBoundary_times E_EdgeCorner_times, -- Needs disjointness or subadditivity
    -- E_SafeBoundary_times and E_EdgeCorner_times are disjoint by def of set difference.
    -- apply measure_union_le, -- if not disjoint use subadditivity
    refine (measure_union_le _ _).trans_eq (by rw [h_vol_SafeBoundary_zero, h_vol_EdgeCorner_zero_interval, add_zero]),
    exact le_trans (measure_mono E_γ_subset_frontier_times) (by assumption),
  },

  -- The integral is over a set of measure zero, so it's zero.
  -- Need lintegral_indicator_eq_lintegral_restrict
  -- Then lintegral_eq_zero_of_measure_zero
  let F_indicator := (SafeSet n ε_global).indicator (fun (_ : ParameterSpace n) => 1 : ℝ≥0∞),
  let G_path := fun t_val : ℝ => γ ⟨t_val, sorry_cast_nonneg_interval (mem_Ioo.mp ‹_›).1⟩,
  have : ∫⁻ (t : ℝ) in E_γ_times, F_indicator (G_path t) = ∫⁻ (t : ℝ) in E_γ_times, 1,
  { apply set_lintegral_congr_fun (measurable_const.indicator (measurableSet_E_gamma_times sorry)), -- E_γ_times needs to be measurable
    filter_upwards [ae_restrict_mem (measurableSet_E_gamma_times sorry)] with t ht_in_E_gamma,
    simp only [E_γ_times, mem_setOf_eq] at ht_in_E_gamma,
    simp [indicator_of_mem ht_in_E_gamma.2],
  },
  rw [this, lintegral_one_eq_volume_ennreal, measure_congr volume_of_ne_mem_of_volume_zero (sorry_E_gamma_complement_proof h_vol_E_gamma_zero), measure_empty],
  -- This part needs refinement: if measure E_γ_times = 0, then integral is 0.
  -- lintegral_eq_zero_iff implies integrand is ae zero.
  -- More direct: lintegral_mono_set
  rw lintegral_eq_zero_iff',
  refine ⟨(Measurable.indicator sorry_measurable_SafeSet measurable_const).comp_aefun sorry_measurable_gamma, _⟩,
  filter_upwards [ae_restrict_mem (measurableSet_Ioo)] with t ht_in_interval,
  by_cases h_in_E_gamma : t ∈ E_γ_times,
  { -- If t is in E_γ_times, this should mean something for the indicator.
    -- But E_γ_times has measure zero, so this case is "ignored" by ae.
    -- Need to show that {t ∈ Ioo 0 T_val | F_indicator (G_path t) ≠ 0} has measure zero.
    -- F_indicator is 1 if G_path(t) ∈ SafeSet, 0 otherwise.
    -- So this set is exactly E_γ_times.
    exact h_vol_E_gamma_zero,
  },
  { -- t ∉ E_γ_times => G_path(t) ∉ SafeSet => Indicator is 0.
    simp only [E_γ_times, mem_setOf_eq, not_and, not_imp_not] at h_in_E_gamma,
    simp [indicator_of_not_mem (h_in_E_gamma ht_in_interval)],
  }
end


-- Main Theorem (Topological Trap)
theorem topological_alignment_trap_with_axioms
  -- Probability space for paths
  [MeasureSpace (TrainingPath n)] [IsProbabilityMeasure (ℙ : Measure (TrainingPath n))]
  -- Assume almost all paths satisfy our conditions & axioms
  (h_ae_C1 : ∀ᵐ γ ∂ℙ, ∀ t : ℝ≥0, DifferentiableAt ℝ (fun s : ℝ => γ ⟨s, sorry_cast_nonneg⟩) t.val)
  (h_ae_starts_outside : ∀ᵐ γ ∂ℙ, γ 0 ∉ SafeSet n ε_global)
  (h_ae_Axiom1 : ∀ᵐ γ ∂ℙ,
    ∀ t_nnreal : ℝ≥0, γ t_nnreal ∈ SafeBoundary n ε_global →
      ∃ (i : Fin n), IsOnFace γ t_nnreal ε_global i ∧ IsOutwardNormalDerivAtFace γ t_nnreal ε_global i)
  (h_ae_Axiom2 : ∀ᵐ γ ∂ℙ,
    {t_val : ℝ | ⟨t_val, sorry_cast_nonneg⟩ ∈ {t' : ℝ≥0 | γ t' ∈ interior (SafeSet n ε_global)}} = ∅)
  (h_ae_Axiom3 : ∀ᵐ γ ∂ℙ,
    volume {t_val : ℝ | ⟨t_val, sorry_cast_nonneg⟩ ∈
      {t' : ℝ≥0 | γ t' ∈ (frontier (SafeSet n ε_global) \ SafeBoundary n ε_global)}} = 0) :
  ℙ { γ_path | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0
         ∧ γ_path t_nnreal ∈ SafeSet n ε_global
         ∧ (∀ s_val ∈ Set.Ioo t_nnreal.val (t_nnreal.val + 1),
              γ_path ⟨s_val, by simpa using (mem_Ioo.1 ‹_›).1⟩ ∈ SafeSet n ε_global) } = 0 :=
begin
  let ProblematicPaths := { γ_path | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0
    ∧ γ_path t_nnreal ∈ SafeSet n ε_global
    ∧ (∀ s_val ∈ Set.Ioo t_nnreal.val (t_nnreal.val + 1),
        γ_path ⟨s_val, by simpa using (mem_Ioo.1 ‹_›).1⟩ ∈ SafeSet n ε_global) },

  -- We want to show that any path γ satisfying the AE conditions is NOT in ProblematicPaths.
  -- Then ProblematicPaths is a subset of a null set, so it's null.
  apply measure_zero_of_ae_not_mem,
  filter_upwards [h_ae_C1, h_ae_starts_outside, h_ae_Axiom1, h_ae_Axiom2, h_ae_Axiom3]
    with γ_current hγc_C1 hγc_starts_out hγc_Ax1 hγc_Ax2 hγc_Ax3,

  -- Assume for contradiction that γ_current ∈ ProblematicPaths
  intro h_γ_current_problematic,
  rcases h_γ_current_problematic with ⟨t_entry_nnreal, ht_entry_pos, h_γ_entry_in_safe, h_γ_stays_in⟩,

  let T_observe := t_entry_nnreal.val + 2,
  have hT_observe_pos : T_observe > 0 := by linarith [NNReal.val_pos.mp ht_entry_pos],

  -- For this γ_current, the occupation time integral is zero
  have int_is_zero : ∫⁻ (t : ℝ) in Ioo 0 T_observe, (SafeSet n ε_global).indicator (fun _ => 1)
      (γ_current ⟨t, sorry_cast_nonneg_interval (mem_Ioo.mp ‹_›).1⟩) = 0,
  { apply zero_occupation_time_helper_with_axioms γ_current hγc_C1 hγc_starts_out
      hγc_Ax1 hγc_Ax2 hγc_Ax3 hT_observe_pos, },

  -- But if it stays in for 1 unit, the integral is positive
  have int_is_positive : ∫⁻ (t : ℝ) in Ioo 0 T_observe, (SafeSet n ε_global).indicator (fun _ => 1)
      (γ_current ⟨t, sorry_cast_nonneg_interval (mem_Ioo.mp ‹_›).1⟩) > 0,
  { let sub_interval := Ioo t_entry_nnreal.val (t_entry_nnreal.val + 1),
    have h_sub_interval_nonempty : sub_interval.nonempty := by {simp, linarith [NNReal.val_pos.mp ht_entry_pos]},
    have h_sub_interval_subset_observe : sub_interval ⊆ Ioo 0 T_observe,
    { intros x hx_sub, split,
      { linarith [(NNReal.val_pos.mp ht_entry_pos), (mem_Ioo.mp hx_sub).1], },
      { linarith [(mem_Ioo.mp hx_sub).2], }
    },
    suffices h_integral_on_sub_interval_is_one :
      ∫⁻ t in sub_interval, (SafeSet n ε_global).indicator (fun (_x : ParameterSpace n) => 1)
        (γ_current ⟨t, sorry_cast_nonneg_interval (mem_Ioo.mp ‹_›).1⟩) = ENNReal.ofReal 1,
    { have h_mono_integral := lintegral_mono_set h_sub_interval_subset_observe, -- Needs integrand non-neg
      rw [← h_integral_on_sub_interval_is_one] at h_mono_integral,
      apply gt_of_ge_of_gt h_mono_integral,
      exact ENNReal.one_pos,
    },
    apply set_lintegral_congr_fun (Measurable.indicator sorry_mble_SafeSet measurable_const).aemeasurable (measurable_const.aemeasurable), -- Need measurability
    { filter_upwards [ae_restrict_mem measurableSet_Ioo] with s_val hs_in_sub_interval,
      specialize h_γ_stays_in s_val hs_in_sub_interval,
      simp [indicator_of_mem h_γ_stays_in], },
    { simp [lintegral_one, Real.volume_Ioo, ENNReal.ofReal_one], }, -- volume is (t+1)-t = 1
  },
  linarith [int_is_zero, int_is_positive.le], -- Contradiction 0 < 0 (from 0 = int > 0)
end

-- sorry_cast_nonneg would be something like:
-- lemma sorry_cast_nonneg (t_val : ℝ) (ht_nonneg : t_val ≥ 0) : ℝ≥0 := ⟨t_val, ht_nonneg⟩
-- And sorry_cast_nonneg_interval for t_val coming from Ioo 0 T ensures t_val ≥ 0 if T > 0.
-- Similar for `mem_of_mem_safe_boundary`, `SafeBoundary_subset_frontier`, etc.
-- `measurableSet_E_gamma_times` would need γ to be measurable and SafeSet measurable.
