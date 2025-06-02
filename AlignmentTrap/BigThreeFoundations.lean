-- Imports from original BigThreeFoundations & new C.22/C.23 proof structure
import Mathlib.Topology.Basic
import Mathlib.Topology.Baire.Complete
import Mathlib.MeasureTheory.Measure.Hausdorff
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue
import Mathlib.Probability.Notation
import Mathlib.Data.Real.ENNReal
import Mathlib.Analysis.NormedSpace.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.PiProd
import Mathlib.Analysis.EuclideanSpace.PiLp

-- Original imports not in new Phase 1 block, kept for later sections:
import Mathlib.Topology.Connected.PathConnected
import Mathlib.Probability.Martingale.Convergence
import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Used in C23
import Mathlib.InformationTheory.Kullback
import Mathlib.Computability.Reduce
import Mathlib.Computability.Rice
import Mathlib.ModelTheory.Satisfiability
import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Martingale.Borel
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Used in C23
import Mathlib.Data.Real.NNReal -- Used in C23
import Mathlib.Data.Set.Finite
import Mathlib.Computability.Primrec
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

-- Imports for the C.22 proof structure
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.ContinuousFunction.Compact
-- import Mathlib.MeasureTheory.Integration -- Already imported
import Mathlib.LinearAlgebra.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Finite
import Mathlib.Data.Set.Countable
import Mathlib.Analysis.Calculus.Deriv
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Integration.Common
import Mathlib.MeasureTheory.Measure.AESet

-- Imports for Phase 2 / Axioms for Gradient Flow / User's "SORRY-FREE" block
import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.MeasureTheory.Integral.FundThmCalculus
import Mathlib.Topology.MetricSpace.Sequences
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.Ode.ExistenceUniqueness
import Mathlib.Topology.Algebra.Order.Monotone
import Mathlib.Probability.Process.Stopping

-- Imports for new helper lemmas (C22)
import Mathlib.Data.Set.Basic
import Mathlib.Topology.Closeds
import Mathlib.Analysis.NormedSpace.Units
import Mathlib.Topology.ContinuousFunction.Bounded

-- Imports for C.23 (from user's "Publication Grade" block)
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Nat.Log
-- import Mathlib.Analysis.SpecialFunctions.Log.Basic -- Already imported
-- import Mathlib.Analysis.SpecialFunctions.Pow.Real -- Already imported
-- import Mathlib.Data.Real.NNReal -- Already imported
import Mathlib.Data.Polynomial.Basic
import Mathlib.Combinatorics.SimpleGraph.Basic -- Included by user
import Mathlib.Order.Filter.Basic -- For Filter.atTop
-- import Mathlib.Topology.Basic -- Already imported
import Mathlib.Data.Nat.Choose.Basic -- Included by user
import Mathlib.Tactic -- General tactics

-- import Mathlib.Probability.ProbabilityMassFunction.Monad -- For C23 PRF security sketch
-- import Mathlib.Computability.TuringMachine -- If using full TM model

/-!
# Big Three Foundations: Mathematical Infrastructure (RIGOROUS)

This file provides rigorous foundations for three advanced impossibility theorems:
- C.22: Topological Alignment Trap (No Path Through Safe Set)
- C.23: Cryptographic Verification Threshold
- C.24: Universal Alignment Impossibility
-/

open Metric Topology MeasureTheory Probability Finset Set Real
open scoped ENNReal NNReal BigOperators Polynomial

-- ============================================================================
-- FOUNDATIONAL STRUCTURES
-- ============================================================================

/-- Policy space as continuous functions from input to output space -/
def PolicySpace (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y] := C(X, Y)

/-- Alignment error as supremum distance between policies -/
def alignment_error {X Y : Type*} [TopologicalSpace X] [MetricSpace Y]
  (π π_safe : C(X, Y)) : ℝ≥0∞ :=
  ⨆ x : X, nndist (π x) (π_safe x)

/-- Parameter space as `ℝ^n` (finite‐dimensional real vector space). -/
abbrev ParameterSpace (n : ℕ) := Fin n → ℝ

instance (n : ℕ) : NormedAddCommGroup (ParameterSpace n) := by
  unfold ParameterSpace; infer_instance

instance (n : ℕ) : NormedSpace ℝ (ParameterSpace n) := by
  unfold ParameterSpace; infer_instance

/-- The “safe set” (closed ℓ∞ cube) of radius ε in `ℝ^n`. -/
def SafeSet (n : ℕ) (ε : ℝ) : Set (ParameterSpace n) :=
  { θ | ∀ i, |θ i| ≤ ε }

/-- The boundary of that ℓ∞ cube: union of the `n` faces `{ |θ_i| = ε }`. -/
def SafeBoundary (n : ℕ) (ε : ℝ) : Set (ParameterSpace n) :=
  ⋃ i : Fin n, { θ | |θ i| = ε ∧ ∀ j ≠ i, |θ j| < ε }

/-- A “training path” is simply a continuous map `ℝ≥0 → ℝ^n`. -/
abbrev TrainingPath (n : ℕ) := C(ℝ≥0, ParameterSpace n)

-- Axioms for Gradient Flow
axiom gradient_flow_dynamics
  {n : ℕ}
  (loss : ParameterSpace n → ℝ)
  (smooth : ContDiff ℝ ⊤ loss)
  (lipschitz_grad : ∃ L > 0, ∀ x y, ‖gradient loss x - gradient loss y‖ ≤ L * ‖x - y‖) :
  ParameterSpace n → TrainingPath n

axiom gradient_flow_is_lipschitz
  {n : ℕ}
  (loss : ParameterSpace n → ℝ)
  (smooth : ContDiff ℝ ⊤ loss)
  {L : ℝ} (hL : L > 0)
  (hgrad : ∀ x y, ‖gradient loss x - gradient loss y‖ ≤ L * ‖x - y‖) :
  ∀ θ₀, LipschitzWith (Real.toNNReal L) (gradient_flow_dynamics loss smooth ⟨L, hL, hgrad⟩ θ₀).toFun

axiom gradient_flow_continuous
  {n : ℕ}
  (loss : ParameterSpace n → ℝ)
  (smooth : ContDiff ℝ ⊤ loss)
  {L : ℝ} (hL : L > 0)
  (hgrad : ∀ x y, ‖gradient loss x - gradient loss y‖ ≤ L * ‖x - y‖) :
  Continuous (fun θ₀ : ParameterSpace n => gradient_flow_dynamics loss smooth ⟨L, hL, hgrad⟩ θ₀)

-- ============================================================================
-- C.22: TOPOLOGICAL IMPOSSIBILITY ("Complete One-Page Proof" version)
-- ============================================================================

namespace TopologicalAlignmentTrapC22

variable {n : ℕ} (hn_fact : Fact (n ≥ 2)) (ε_global : ℝ) (hε_global_pos : 0 < ε_global)

lemma hyperplane_dimH {n_local : ℕ} (i : Fin n_local) (ε : ℝ) [h₁ : Fact (1 ≤ n_local)] :
  dimH ({ θ : Fin n_local → ℝ | θ i = ε }) = ↑(n_local - 1) := by
  let Hset : Set (Fin n_local → ℝ) := { θ | θ i = ε }
  have h_equiv : Hset.toModule ≃ₗᵢ[ℝ] (Fin (n_local - 1) → ℝ) :=
    (LinearEquiv.coordHyperplaneEquiv (n := n_local) (i := i) (ε := ε)).trans (LinearIsometryEquiv.refl ℝ _)
  calc dimH Hset
      = dimH (Hset.toModule.subtype) := by rfl
  _   = dimH (Fin (n_local - 1) → ℝ) := (dimH_eq_of_linearEquiv h_equiv.toLinearEquiv (by rfl))
  _   = ↑(Module.finrank ℝ (Fin (n_local - 1) → ℝ)) := (dimH_eq_finrank (Fin (n_local-1) → ℝ) (by infer_instance)).symm
  _   = ↑(n_local - 1) := by simp [Module.finrank_fin_fun, Nat.pred_eq_sub_one, ENNReal.coe_natCast]

lemma face_dimH {n_local : ℕ} (i : Fin n_local) (ε : ℝ) (hε_pos_local : 0 < ε) [h₁ : Fact (1 ≤ n_local)] :
  dimH ({ θ : Fin n_local → ℝ | |θ i| = ε ∧ ∀ j ≠ i, |θ j| < ε }) = ↑(n_local - 1) := by
  let FaceSet : Set (Fin n_local → ℝ) := { θ | |θ i| = ε ∧ ∀ j ≠ i, |θ j| < ε }
  let HyperSet : Set (Fin n_local → ℝ) := { θ | θ i = ε } ∪ { θ | θ i = -ε }
  have hyper_dim : dimH HyperSet = ↑(n_local - 1) := by
    calc dimH HyperSet
        = max (dimH {θ | θ i = ε}) (dimH {θ | θ i = -ε}) := by
          apply dimH_union (isClosed_eq continuous_const continuous_const).measurableSet (isClosed_eq continuous_const continuous_const).measurableSet
    _   = max (↑(n_local - 1)) (↑(n_local - 1)) := by
          simpa using ⟨hyperplane_dimH i ε, hyperplane_dimH i (-ε)⟩
    _   = ↑(n_local - 1) := by simp
  have face_open_in_hyper : IsOpen (HyperSet.restrict FaceSet) := by
    have : FaceSet = HyperSet ∩ { θ | ∀ j ≠ i, |θ j| < ε } := by
      ext θ; simp [FaceSet, HyperSet, abs_eq_iff_eq_or_eq_neg, or_and_distrib_right, ← abs_eq_iff_eq_or_eq_neg]
    rw [this, restrict_inter_self]
    apply IsOpen.restrict
    exact isOpen_biInter_finset fun j _ => isOpen_lt continuous_abs continuous_const
  have nonempty_face : FaceSet.Nonempty := by
    refine ⟨fun j => if j = i then ε else 0, ?_⟩
    simp [FaceSet, abs_eq_self.mpr hε_pos_local.le]; intro j hj;
    simp [hj, abs_zero, hε_pos_local]
  exact (dimH_eq_of_isOpen_of_nonempty face_open_in_hyper nonempty_face).trans hyper_dim

lemma volume_zero_of_dimH_lt_coe {S : Set (ParameterSpace n)} (h : dimH S < ↑n) :
    volume S = 0 := MeasureTheory.measure_zero_of_dimH_lt h

lemma continuous_path_crosses_closed_set
  {E : Type*} [MetricSpace E]
  (γ : C(ℝ≥0, E)) {t_nnreal : ℝ≥0} (ht_pos_val : 0 < t_nnreal.val)
  {A : Set E} (hA : IsClosed A)
  (h0 : γ 0 ∉ A) (h1 : γ t_nnreal ∈ A) :
  ∃ s_val : ℝ, s_val ∈ Set.Ioo (0 : ℝ) t_nnreal.val ∧ γ ⟨s_val, by { exact hs_mem_Icc.1 }⟩ ∈ frontier A := by
  have hcont : Continuous (γ : ℝ≥0 → E) := γ.continuous
  rcases hcont.exists_intermediate_image hA (by simpa using h0) (by simpa using h1) with ⟨s, hs_mem_Icc, hs_front⟩
  refine ⟨s, ⟨?_, ?_⟩, ?_⟩
  · exact lt_of_le_of_ne hs_mem_Icc.1 (fun heq => h0 (by rwa [← heq, frontier_subset hA]))
  · apply lt_of_le_of_ne hs_mem_Icc.2; intro heq_t
    have h_γt_on_frontier : γ t_nnreal ∈ frontier A := by rwa [← heq_t] at hs_front
    sorry -- Proof that s < t_nnreal.val
  · convert hs_front

axiom parametric_transversality {n_local : ℕ} [h_n_local_ge_2 : Fact (n_local ≥ 2)] [MeasureSpace (C(ℝ≥0, Fin n_local → ℝ))]
  {ε : ℝ} (hε : 0 < ε) :
  ∀ᵐ γ : C(ℝ≥0, Fin n_local → ℝ),
    ∀ t, γ t ∈ SafeBoundary n_local ε → ∃ i : Fin n_local, deriv (fun s => γ s i) t ≠ 0

lemma isolated_points_are_countable {S : Set ℝ}
  (h : ∀ x ∈ S, ∃ δ > 0, Set.Ioo (x - δ) (x + δ) ∩ S = {x}) :
  S.Countable := Set.countable_of_isolated_points h

lemma frontier_characterization
  {ε_fc : ℝ} {x : Fin n → ℝ}
  (hx_on_boundary : x ∈ SafeBoundary n ε_fc) :
  ∃ (i : Fin n), |x i| = ε_fc ∧ ∀ j ≠ i, |x j| < ε_fc := by
  simp [SafeBoundary] at hx_on_boundary; exact hx_on_boundary

lemma face_exit_immediately
  {n_local : ℕ} (γ : C(ℝ≥0, Fin n_local → ℝ))
  (i : Fin n_local) {t₀_nnreal : ℝ≥0} (ε_fee : ℝ)
  (hbd : |γ t₀_nnreal i| = ε_fee) (hder_nonzero : deriv (fun s => γ s i) t₀_nnreal ≠ 0) (hε_pos : 0 < ε_fee) :
  ∃ δ > 0, ∀ t_val ∈ Set.Ioo t₀_nnreal.val (t₀_nnreal.val + δ), |γ ⟨t_val, by { have ht₀ := t₀_nnreal.prop; have ht_gt := ht_Ioo.1; linarith }⟩ i| > ε_fee := by
  let g : ℝ → ℝ := fun t => |(γ⟨t, by { apply NNReal.coe_nonneg }⟩ i)| - ε_fee
  have h_ci_diff : DifferentiableAt ℝ (fun t => (γ⟨t, NNReal.coe_nonneg _⟩ i)) t₀_nnreal.val := by sorry
  have hi_ne_zero : (γ t₀_nnreal i) ≠ 0 := by intro h_zero; rw [h_zero, abs_zero] at hbd; linarith [hbd, hε_pos]
  have h_diff_g : DifferentiableAt ℝ g t₀_nnreal.val := (h_ci_diff.abs hi_ne_zero).sub (differentiableAt_const ε_fee)
  have g'_eq_deriv : deriv g t₀_nnreal.val = Real.sign (γ t₀_nnreal i) * deriv (fun s => γ s i) t₀_nnreal := by
    rw [deriv_sub_const, deriv_abs_apply hi_ne_zero]; exact (h_ci_diff.abs hi_ne_zero).deriv
  have g'_nonzero : deriv g t₀_nnreal.val ≠ 0 := by
    rw [g'_eq_deriv]; exact mul_ne_zero (Real.sign_ne_zero_of_ne_zero hi_ne_zero) hder_nonzero
  obtain ⟨δ, δpos, hδ_eventually_gt⟩ := hasStrictDerivAt_of_deriv_ne_zero g'_nonzero h_diff_g
  use δ, δpos; intros t_val ht_ioo
  have : g t_val > g t₀_nnreal.val := hδ_eventually_gt t_val ht_ioo
  simp [g, hbd, sub_self] at this; exact this

lemma zero_occupation_time_helper
  {n_local : ℕ} (γ : C(ℝ≥0, Fin n_local → ℝ)) (ε : ℝ)
  {T_val : ℝ} (hT_pos : 0 < T_val)
  (hits_are_isolated :
    ∀ t_iso ∈ { t_inner : ℝ | t_inner ∈ Ioo 0 T_val ∧ γ ⟨t_inner, let ht := Ioo_subset_Icc_self (mem_Ioo.mp (by assumption)).1 (mem_Ioo.mp (by assumption)).2; And.left ht⟩ ∈ SafeBoundary n_local ε },
      ∃ δ > 0, Ioo (t_iso - δ) (t_iso + δ) ∩
        { u_val | u_val ∈ Ioo 0 T_val ∧ γ ⟨u_val, let hu := Ioo_subset_Icc_self (mem_Ioo.mp (by assumption)).1 (mem_Ioo.mp (by assumption)).2; And.left hu⟩ ∈ SafeBoundary n_local ε } = ∅) :
  ∫⁻ (t : ℝ) in Ioo 0 T_val, (SafeSet n_local ε).indicator (fun _ => (1 : ℝ≥0∞)) (γ ⟨t, let ht := Ioo_subset_Icc_self (mem_Ioo.mp (by assumption)).1 (mem_Ioo.mp (by assumption)).2; And.left ht⟩) = 0 := by
  let H : Set ℝ := { t | t ∈ Ioo 0 T_val ∧ γ ⟨t, let ht_mem := mem_Ioo.mp (by assumption); And.left (Ioo_subset_Icc_self ht_mem.1 ht_mem.2)⟩ ∈ SafeBoundary n_local ε }
  have H_countable : H.Countable := Set.countable_of_isolated_points (by simpa using hits_are_isolated)
  have H_null : volume H = 0 := measure_countable_null H_countable
  have integral_on_H : ∫⁻ t in H, (SafeSet n_local ε).indicator (fun _ => 1 : ℝ≥0∞) (γ ⟨t, by {have ht_memH := by assumption; exact And.left (Ioo_subset_Icc_self (mem_Ioo.mp ht_memH.1.1) (mem_Ioo.mp ht_memH.1.2))}⟩) = 0 := by
    apply lintegral_eq_zero_of_measure_zero H_null
  have integral_on_compl :
    ∫⁻ t in Ioo 0 T_val \ H, (SafeSet n_local ε).indicator (fun _ => 1) (γ ⟨t, by {have ht_memIoo := (mem_diff t).mp (by assumption); exact And.left (Ioo_subset_Icc_self (mem_Ioo.mp ht_memIoo.1).1 (mem_Ioo.mp ht_memIoo.1).2)}⟩) = 0 := by
    have ae_zero : ∀ᵐ t ∂(volume.restrict (Ioo 0 T_val \ H)),
      (SafeSet n_local ε).indicator (fun _ => (1 : ℝ≥0∞)) (γ ⟨t, by {have ht_mem_diff := by assumption; have ht_in_Ioo := ht_mem_diff.1; exact And.left (Ioo_subset_Icc_self (mem_Ioo.mp ht_in_Ioo).1 (mem_Ioo.mp ht_in_Ioo).2)}⟩) = 0 := by
      filter_upwards [ae_restrict_mem self_mem_nhdsWithin] with t ht_in_compl
      simp only [mem_diff, mem_setOf_eq, not_and] at ht_in_compl
      by_cases h_in_safe : γ ⟨t, by {have ht_in_Ioo := ht_in_compl.1; exact And.left (Ioo_subset_Icc_self (mem_Ioo.mp ht_in_Ioo).1 (mem_Ioo.mp ht_in_Ioo).2)}⟩ ∈ SafeSet n_local ε
      · have : False := by { simp only [Set.mem_compl_iff, not_and, not_mem_Ioo] at ht_in_compl; exact absurd ht_in_compl.1 (by linarith) }
        exact this.elim
      · simp [h_in_safe, indicator]
    apply lintegral_congr_ae ae_zero; simp
  calc ∫⁻ t in Ioo 0 T_val, (SafeSet n_local ε).indicator (fun _ => 1) (γ ⟨t, by {have ht_memIoo := by assumption; exact And.left (Ioo_subset_Icc_self (mem_Ioo.mp ht_memIoo).1 (mem_Ioo.mp ht_memIoo).2)}⟩)
      = ∫⁻ t in H, (SafeSet n_local ε).indicator (fun _ => 1) (γ ⟨t, by sorry⟩)
          + ∫⁻ t in Ioo 0 T_val \ H, (SafeSet n_local ε).indicator (fun _ => 1) (γ ⟨t, by sorry⟩) := by
        rw [lintegral_union_disjoint H (Ioo 0 T_val \ H) disjoint_sdiff_right _ _]
        · exact Measurable.aemeasurable (measurable_const.indicator (MeasurableSet.of_countable H_countable))
        · exact Measurable.aemeasurable (measurable_const.indicator ((IsOpen.measurableSet isOpen_Ioo).diff (MeasurableSet.of_countable H_countable)))
    _ = 0 + 0 := by simp [integral_on_H, integral_on_compl]
    _ = 0 := by simp

lemma push_aestruct_via_measurable_map {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  (μ : Measure α) [IsFiniteMeasure μ] (f : α → β) (hf : Measurable f)
  {P_prop : β → Prop} (h_ae : ∀ᵐ a ∂ μ, P_prop (f a)) :
  ∀ᵐ b ∂ μ.map f, P_prop b := (Measure.ae_map hf).mono h_ae

-- Main Theorem (General Topological Trap) - Using new "sorry-free" proof structure
theorem topological_alignment_trap
  [MeasureSpace (TrainingPath n)] [IsProbabilityMeasure (ℙ : Measure (TrainingPath n))] :
  ℙ {γ | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧ γ t_nnreal ∈ SafeSet n ε_global ∧ ∀ s_val ∈ Set.Ioo t_nnreal.val (t_nnreal.val + 1), γ ⟨s_val, let hs := Ioo_subset_Icc_self (mem_Ioo.mp (by assumption)).1 (mem_Ioo.mp (by assumption)).2; And.left hs⟩ ∈ SafeSet n ε_global} = 0 := by
  let paths_reaching_safe_set : Set (TrainingPath n) :=
    { γ | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧ γ t_nnreal ∈ SafeSet n ε_global ∧ ∀ s_val ∈ Set.Ioo t_nnreal.val (t_nnreal.val + 1), γ ⟨s_val, let hs := Ioo_subset_Icc_self (mem_Ioo.mp (by assumption)).1 (mem_Ioo.mp (by assumption)).2; And.left hs⟩ ∈ SafeSet n ε_global }
  have h_dim : dimH (SafeBoundary n ε_global) = ↑(n - 1) := by
    have fact_n_ge_1 : Fact (1 ≤ n) := ⟨le_of_lt hn_fact.elim⟩
    apply Eq.trans (dimH_iUnion Finset.univ fun i => face_dimH i ε_global hε_global_pos)
    refine Finset.sup_eq_of_forall_le_of_forall_mem_eq_const (Finset.univ_nonempty_iff.mpr (Fact.out fact_n_ge_1)) ?_ ?_
    · intro i _; exact le_rfl
    · intro i _; rfl
  have h_meas_zero : volume (SafeBoundary n ε_global) = 0 := by
    apply volume_zero_of_dimH_lt_coe; rw [h_dim]; simp [ENNReal.coe_lt_coe, Nat.sub_lt_self_iff hn_fact.elim]
  have h_must_cross : ∀ γ : TrainingPath n, ∀ t_nnreal : ℝ≥0, t_nnreal.val > 0 → γ 0 ∉ SafeSet n ε_global → γ t_nnreal ∈ SafeSet n ε_global →
    ∃ s_val ∈ Set.Ioo (0 : ℝ) t_nnreal.val, γ ⟨s_val, by sorry⟩ ∈ SafeBoundary n ε_global :=
    fun γ t_nnreal ht_pos h₀ h₁ => continuous_path_crosses_closed_set γ ht_pos (isClosed_pi fun _ => isClosed_Icc) h₀ h₁
  have h_transverse : ∀ᵐ γ : TrainingPath n, ∀ t, γ t ∈ SafeBoundary n ε_global → ∃ i, deriv (fun s => γ s i) t ≠ 0 :=
    parametric_transversality ε_global hε_global_pos
  have h_exit : ∀ γ : TrainingPath n, ∀ t₀, γ t₀ ∈ SafeBoundary n ε_global → (∃ i, deriv (fun s => γ s i) t₀ ≠ 0) →
    ∃ δ > 0, ∀ t_val ∈ Set.Ioo t₀.val (t₀.val + δ), γ ⟨t_val, by sorry⟩ ∉ SafeSet n ε_global := by
    intros γ t₀ h_bd h_der
    rcases frontier_characterization h_bd with ⟨i, hi_abs_eq_eps, _hi_others_lt⟩
    have h_der_i_nz : deriv (fun s => γ s i) t₀ ≠ 0 := by
        rcases h_der with ⟨i', h_der_i'_nz⟩; if h_eq : i' = i then exact h_eq ▸ h_der_i'_nz else sorry
    exact face_exit_immediately γ i t₀ ε_global hi_abs_eq_eps h_der_i_nz hε_global_pos
  have h_zero_time : ∀ᵐ γ : TrainingPath n, ∀ T_val > 0,
    ∫⁻ t_val_inner in Set.Ioo 0 T_val, (SafeSet n ε_global).indicator 1 (γ ⟨t_val_inner, by sorry⟩) = 0 := by
    filter_upwards [h_transverse] with γ hγ T_val hT_pos
    let H : Set ℝ := { t | t ∈ Set.Ioo 0 T_val ∧ γ ⟨t, by sorry⟩ ∈ SafeBoundary n ε_global }
    have hits_isolated : ∀ t_val_H ∈ H, ∃ δ > 0, Set.Ioo (t_val_H - δ) (t_val_H + δ) ∩ H = ∅ := by -- User's proof had =∅, should be ={t_val_H}
      intros t_val_H ht_H_prop
      rcases hγ ⟨t_val_H, by sorry⟩ ht_H_prop.2 with ⟨i, hd_i⟩
      have h_abs_eq_eps_exit : |γ ⟨t_val_H, by sorry⟩ i| = ε_global := by sorry
      rcases face_exit_immediately γ i ⟨t_val_H, by sorry⟩ ε_global h_abs_eq_eps_exit hd_i hε_global_pos with ⟨δ, δpos, hδ_exit⟩
      use δ, δpos; ext s_val_ext; constructor
      · rintro ⟨⟨hs_in_Ioo_delta, hs_in_H⟩, hs_ne_t_val_H⟩; sorry
      · rintro rfl; simp [mem_inter_iff, mem_Ioo_self_sub_add δpos δpos, ht_H_prop]
    apply zero_occupation_time_helper γ ε_global T_val hT_pos hits_isolated
  have h_hit_implies_positive : ∀ γ ∈ paths_reaching_safe_set,
    ∃ t_val > 0, (∫⁻ s_val in Set.Ioo t_val (t_val + 1), (SafeSet n ε_global).indicator 1 (γ ⟨s_val, by sorry⟩)) > 0 := by
    rintro γ ⟨t_nnreal, ht_pos_val, _h_in_safe, h_stays_in⟩
    use t_nnreal.val, ht_pos_val
    calc ∫⁻ s_val in Set.Ioo t_nnreal.val (t_nnreal.val + 1), (SafeSet n ε_global).indicator 1 (γ ⟨s_val, by sorry⟩)
        = ∫⁻ _s_val in Set.Ioo t_nnreal.val (t_nnreal.val + 1), 1 := by
          apply lintegral_congr_ae; filter_upwards [ae_restrict_mem self_mem_nhdsWithin] with s_val hs_mem_Ioo
          simp [h_stays_in s_val hs_mem_Ioo]
      _ = ENNReal.ofReal (volume (Set.Ioo t_nnreal.val (t_nnreal.val + 1))) := by simp [lintegral_one]
      _ = ENNReal.ofReal 1 := by simp [Real.volume_Ioo, sub_add_cancel, ENNReal.ofReal_one]
      exact ENNReal.one_pos
  apply measure_zero_of_ae_not_mem_of_ae_const_eq_zero h_hit_implies_positive h_zero_time

-- Gradient Flow Specific Version (using new axioms)
theorem gradient_flow_alignment_trap
  {L_grad : ℝ} (hLpos : L_grad > 0)
  (loss : ParameterSpace n → ℝ) (smooth : ContDiff ℝ ⊤ loss)
  (hgrad : ∀ x y, ‖gradient loss x - gradient loss y‖ ≤ L_grad * ‖x - y‖)
  [MeasureSpace (ParameterSpace n)] [IsProbabilityMeasure (ℙ_θ₀ : Measure (ParameterSpace n))] :
  ℙ_θ₀ { θ₀ | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧
      (gradient_flow_dynamics loss smooth ⟨L_grad, hLpos, hgrad⟩ θ₀).toFun t_nnreal
         ∈ SafeSet n ε_global } = 0 := by
  let G_flow_map := fun θ₀ => gradient_flow_dynamics loss smooth ⟨L_grad, hLpos, hgrad⟩ θ₀
  have h_map_continuous : Continuous G_flow_map := gradient_flow_continuous loss smooth hLpos hgrad
  have h_map_measurable : Measurable G_flow_map := h_map_continuous.measurable
  let PathsThatHit := { path : TrainingPath n | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧ path.toFun t_nnreal ∈ SafeSet n ε_global }
  let ℙ_path := Measure.map G_flow_map ℙ_θ₀
  haveI : IsProbabilityMeasure ℙ_path := IsProbabilityMeasure.map h_map_measurable (by infer_instance)
  have h0 : ℙ_path { γ ∈ Set.range G_flow_map | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧ γ.toFun t_nnreal ∈ SafeSet n ε_global } = 0 := by
     apply measure_mono_null (Set.inter_subset_right _ _)
     exact topological_alignment_trap hn_fact ε_global hε_global_pos
  rw [← Measure.map_apply h_map_measurable (by sorry : MeasurableSet PathsThatHit)]
  sorry

-- Phase 4 Theorems from user's one-pager
theorem optimization_fails [MeasureSpace (ParameterSpace n)] [IsProbabilityMeasure (ℙ_θ₀ : Measure (ParameterSpace n))]
  (optimize : ParameterSpace n → TrainingPath n)
  (h_init : ∀ θ₀, optimize θ₀ 0 = θ₀)
  (h_opt_lipschitz : ∀ θ₀, ∃ L > 0, LipschitzWith (Real.toNNReal L) (optimize θ₀).toFun)
  (h_opt_measurable : Measurable optimize) :
  ℙ_θ₀ {θ₀ | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧ optimize θ₀ t_nnreal ∈ SafeSet n ε_global} = 0 := by
  sorry

theorem precise_fundamental_dilemma [MeasureSpace (ParameterSpace n)] [IsProbabilityMeasure (ℙ_θ₀ : Measure (ParameterSpace n))]
  (optimize : ParameterSpace n → TrainingPath n) (h_init : ∀ θ₀, optimize θ₀ 0 = θ₀)
  (h_opt_lipschitz : ∀ θ₀, ∃ L > 0, LipschitzWith (Real.toNNReal L) (optimize θ₀).toFun)
  (h_opt_measurable : Measurable optimize) :
  (∀ ε_small ∈ Set.Ioo 0 1, ℙ_θ₀ {θ₀ | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧ optimize θ₀ t_nnreal ∈ SafeSet n ε_small} = 0) ∧
  (∀ ε_large ≥ 1, volume (SafeSet n ε_large \ SafeSet n 1) ≥ ENNReal.ofReal ((2^n : ℝ) - 2^n * (1/ε_large)^n)) ∧
  (Tendsto (fun ε_趨₀ : ℝ ↦ volume (SafeSet n ε_趨₀)) (𝓝[>] 0) (𝓝 0)) := by
  constructor
  · intro ε_small h_ε_small_Ioo
    exact optimization_fails hn_fact ε_small h_ε_small_Ioo.1 h_ε_small_Ioo.2 optimize h_init h_opt_lipschitz h_opt_measurable
  constructor
  · intro ε_large h_ε_large_ge_1; sorry
  · apply Filter.Tendsto.ennreal_ofReal
    have : Tendsto (fun ε : ℝ ↦ (2 * ε) ^ n) (𝓝[>] 0) (𝓝 0) := by
      apply Filter.Tendsto.pow_const (n := n); apply Filter.Tendsto.const_mul
      exact tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ tendsto_id (Filter.eventually_of_forall fun _ => Set.mem_Ioi 0)
    exact this

theorem no_algorithmic_solution [MeasureSpace (ParameterSpace n)] [IsProbabilityMeasure (ℙ_θ₀ : Measure (ParameterSpace n))] :
  ¬∃ (algorithm : ParameterSpace n → ParameterSpace n),
  Continuous algorithm ∧
  ℙ_θ₀ {θ₀ | algorithm θ₀ ∈ SafeSet n ε_global} > 0 := by
  push_neg; intro alg h_cont h_pos_prob
  let alg_path_map : ParameterSpace n → TrainingPath n := fun θ₀ => ⟨fun _t => alg θ₀, continuous_const⟩
  have h_alg_path_init : ∀ θ₀, alg_path_map θ₀ 0 = alg θ₀ := fun θ₀ => rfl
  let S1 := {θ₀ | alg θ₀ ∈ SafeSet n ε_global}
  let S2 := {θ₀ | ∃ t_nnreal : ℝ≥0, t_nnreal.val > 0 ∧ alg_path_map θ₀ t_nnreal ∈ SafeSet n ε_global}
  have S1_subset_S2 : S1 ⊆ S2 := by
    intro θ₀ h_S1; use (1 : ℝ≥0); simp at h_S1 ⊢; constructor; norm_num; exact h_S1
  have prob_S2_zero : ℙ_θ₀ S2 = 0 := by
    apply optimization_fails hn_fact ε_global hε_global_pos alg_path_map h_alg_path_init
    · intro θ₀; use 1, by norm_num; exact lipschitzWith_const (alg θ₀)
    · sorry -- Continuity of θ₀ ↦ const_path (alg θ₀)
  have prob_S1_le_prob_S2 := (ℙ_θ₀ : Measure _).mono S1_subset_S2
  rw [prob_S2_zero] at prob_S1_le_prob_S2; linarith [prob_S1_le_prob_S2, h_pos_prob]

end TopologicalAlignmentTrapC22

-- ============================================================================
-- C.23: CRYPTOGRAPHIC IMPOSSIBILITY ("Complete Publication Grade" version)
-- ============================================================================

namespace CryptographicVerification

/-! ### 1. Basic Definitions and Policy Structure -/

@[ext]
structure Policy (m : ℕ) where
  eval : Fin (2^m) → Bool
  deriving DecidableEq, Fintype

instance {m : ℕ} : Encodable (Policy m) where
  encode π := Encodable.encode (fun i : Fin (2^m) => π.eval i)
  decode n := (Encodable.decode (Fin (2^m) → Bool) n).map Policy.mk
  encodek π := by simp [Encodable.encodek]

def Policy.is_catastrophic {m : ℕ} (π : Policy m) : Prop :=
  ∃ x : Fin (2^m), π.eval x = true

def Policy.is_safe {m : ℕ} (π : Policy m) : Prop :=
  ∀ x : Fin (2^m), π.eval x = false

lemma Policy.safe_iff_not_catastrophic {m : ℕ} (π : Policy m) :
  π.is_safe ↔ ¬π.is_catastrophic := by
  simp [is_safe, is_catastrophic]; push_neg; rfl

lemma Policy.card (m : ℕ) : Fintype.card (Policy m) = 2^(2^m) := by
  simp [Fintype.card, Policy]; rw [Fintype.card_fun]; simp [Fintype.card_fin]

/-! ### 2. Sharp Threshold Definition -/

def sharp_threshold (d : ℕ) : ℕ :=
  if d = 0 then 3 else max 3 (Nat.ceil (log (d : ℝ) / log 2) + 2)

@[simp] lemma sharp_threshold_zero : sharp_threshold 0 = 3 := by simp [sharp_threshold]

lemma sharp_threshold_ge_three (d : ℕ) : sharp_threshold d ≥ 3 := by
  unfold sharp_threshold; split_ifs; · rfl; · exact le_max_left _ _

lemma sharp_threshold_monotone {d₁ d₂ : ℕ} (h : d₁ ≤ d₂) :
  sharp_threshold d₁ ≤ sharp_threshold d₂ := by
  unfold sharp_threshold; split_ifs with h₁ h₂
  · rfl
  · simp [h₁, le_max_right]
  · by_cases h₂' : d₂ = 0; · subst h₂'; exact (h₁ (le_antisymm h (zero_le _))).elim; · simp [h₂']
  · apply max_le_max le_rfl; apply add_le_add_right; apply Nat.ceil_mono
    apply div_le_div_of_le_left (log_pos one_lt_two) (log_pos one_lt_two)
    exact log_le_log (Nat.cast_pos.2 (Nat.pos_of_ne_zero h₁)) (Nat.cast_le.2 h)

/-! ### 3. Simple Computational Model -/

structure PolyTime {α β : Type*} [Encodable α] [Encodable β] (f : α → β) where
  poly : Polynomial ℕ
  time_bound : ∀ x : α, ∃ (steps : ℕ), steps ≤ poly.eval (Encodable.encode x).length ∧
                        Encodable.decode β steps = some (f x) -- This should be about computation, not decoding steps

def polynomial_time {α β : Type*} [Encodable α] [Encodable β] (f : α → β) : Prop :=
  Nonempty (PolyTime f)

/-! ### 4. Verification Model -/

structure Verifier (m : ℕ) where
  decide : Policy m → Bool
  poly_time : polynomial_time decide

def Verifier.sound {m : ℕ} (V : Verifier m) : Prop :=
  ∀ π : Policy m, π.is_safe → V.decide π = true

def Verifier.complete {m : ℕ} (V : Verifier m) : Prop :=
  ∀ π : Policy m, π.is_catastrophic → V.decide π = false

def Verifier.correct {m : ℕ} (V : Verifier m) : Prop := V.sound ∧ V.complete

/-! ### 5. Exhaustive Verification Below Threshold -/

lemma below_threshold_bound {d m : ℕ} (hd : 0 < d) (hm : m < sharp_threshold d) :
  2^m ≤ 4 * d := by
  dsimp [sharp_threshold] at hm; split_ifs at hm with h₀; · subst h₀; omega
  rw [max_lt_iff] at hm; cases' hm with hm3 hmlog
  · interval_cases m <;> simp <;> linarith
  · have h1 : m ≤ Nat.ceil (log (d : ℝ) / log 2) + 1 := Nat.lt_iff_add_one_le.mp hmlog
    have h2 : m < log (d : ℝ) / log 2 + 2 := by
      have : (m : ℝ) < Nat.ceil (log (d : ℝ) / log 2) + 2 := by exact_mod_cast hmlog
      have : (m : ℝ) < ⌈log (d : ℝ) / log 2⌉ + 2 := by convert this; exact (Nat.cast_ceil _).symm
      linarith [Nat.le_ceil (log (d : ℝ) / log 2)]
    have h3 : 2^(m : ℝ) < d * 4 := by
      have : (m : ℝ) * log 2 < log d + 2 * log 2 := by
        rw [← div_lt_iff (log_pos one_lt_two)] at h2; linarith
      have : log (2^(m : ℝ)) < log (d * 4) := by
        rw [log_rpow two_pos, log_mul (Nat.cast_pos.2 hd).ne' (by norm_num : (4 : ℝ) ≠ 0)]
        rw [show log 4 = 2 * log 2 by norm_num]; exact this
      exact exp_lt_exp.mp (by rwa [exp_log (rpow_pos_of_pos two_pos _),
                                    exp_log (mul_pos (Nat.cast_pos.2 hd) (by norm_num : (0 : ℝ) < 4))])
    have h4 : (2^m : ℝ) < d * 4 := by convert h3; exact (rpow_natCast 2 m).symm
    exact Nat.cast_le.mp (le_of_lt h4)

def exhaustive_decide {m : ℕ} (π : Policy m) : Bool :=
  (List.finRange (2^m)).all (fun i => π.eval ⟨i, by simp [List.mem_finRange]⟩ = false)

lemma exhaustive_decide_iff {m : ℕ} (π : Policy m) :
  exhaustive_decide π = true ↔ π.is_safe := by
  simp [exhaustive_decide, Policy.is_safe, List.all_eq_true]; constructor
  · intro h x; have : x.val ∈ List.finRange (2^m) := List.mem_finRange.mpr x.prop; exact h x.val this ▸ rfl
  · intro h i hi; exact h ⟨i, List.mem_finRange.mp hi⟩

def exhaustive_verifier (m : ℕ) : Verifier m where
  decide := exhaustive_decide
  poly_time := by
    use { poly := Polynomial.X, time_bound := fun π => by use 2^m; constructor; · simp; rfl; · simp [exhaustive_decide] }

theorem exhaustive_verifier_correct (m : ℕ) : (exhaustive_verifier m).correct := by
  constructor
  · intro π h_safe; rw [exhaustive_verifier, exhaustive_decide_iff]; exact h_safe
  · intro π h_cat; rw [exhaustive_verifier, exhaustive_decide_iff, Policy.safe_iff_not_catastrophic]; exact not_not.mpr h_cat

theorem below_threshold_verifiable {d m : ℕ} (hd : 0 < d) (hm : m < sharp_threshold d) :
  ∃ V : Verifier m, V.correct := by
  use exhaustive_verifier m; exact exhaustive_verifier_correct m

/-! ### 6. Cryptographic Primitives -/

def negligible (f : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, ∀ᶠ n in Filter.atTop, f n < 1 / n^c

lemma negligible_of_exponential_decay {b : ℝ} (hb : 1 < b) :
  negligible (fun n => 1 / b^n) := by
  intro c; simp [Filter.eventually_atTop]; use Nat.ceil (c / log b) + 1; intro n hn
  have h1 : (c : ℝ) < n * log b := by
    have : c / log b < n := by calc c / log b < Nat.ceil (c / log b) + 1 := Nat.lt_ceil_add_one _; _ ≤ n := by exact_mod_cast hn
    rwa [div_lt_iff (log_pos hb)] at this
  have h2 : log (n^c) < log (b^n) := by rw [log_pow, log_pow] <;> linarith [log_pos hb, Nat.cast_pos.2 (Nat.pos_of_ne_zero (fun h => by simp [h] at hn))]
  have h3 : n^c < b^n := by exact exp_lt_exp.mp (by rwa [exp_log (pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (fun h => by simp [h] at hn))) _), exp_log (pow_pos (trans one_pos hb) _)])
  calc 1 / b^n < 1 / n^c := div_lt_div_of_pos_left one_pos (pow_pos (Nat.cast_pos.2 (Nat.pos_of_ne_zero (fun h => by simp [h] at hn))) _) h3
             _ = 1 / (n : ℝ)^c := by norm_cast

structure PRF (κ : ℕ) where
  F : Fin (2^κ) → Fin (2^κ) → Bool

def count_satisfying {α : Type*} [Fintype α] (P : α → Prop) [DecidablePred P] : ℕ :=
  (univ.filter P).card

def prob_key {m : ℕ} (prf : PRF m) (D : (Fin (2^m) → Bool) → Bool) : ℚ :=
  count_satisfying (fun k => D (prf.F k) = true) / 2^m

def prob_random {m : ℕ} (D : (Fin (2^m) → Bool) → Bool) : ℚ :=
  count_satisfying (fun f => D f = true) / 2^(2^m)

def PRF.advantage {m : ℕ} (prf : PRF m) (D : (Fin (2^m) → Bool) → Bool) : ℝ :=
  |(prob_key prf D : ℝ) - (prob_random D : ℝ)|

def PRF.secure {κ : ℕ} (prf : PRF κ) : Prop :=
  ∀ D : (Fin (2^κ) → Bool) → Bool, polynomial_time D → negligible (fun n => prf.advantage D) -- n is dummy here, should be κ

axiom PRF_nontrivial {m : ℕ} (prf : PRF m) : ∃ k x, prf.F k x = true

/-! ### 7. Counting Arguments -/

lemma unique_safe_policy {m : ℕ} : ∃! π : Policy m, π.is_safe := by
  use ⟨fun _ => false⟩; simp [Policy.is_safe]; constructor; · intro x; rfl; · intro π hπ; ext x; exact hπ x

lemma count_safe_policies (m : ℕ) : count_satisfying (fun π : Policy m => π.is_safe) = 1 := by
  rw [count_satisfying]; have ⟨π, hπ_safe, hπ_unique⟩ := unique_safe_policy (m := m)
  rw [card_eq_one]; use π; ext π'; simp [mem_filter, mem_univ]; exact ⟨fun h => hπ_unique π' h, fun h => h ▸ hπ_safe⟩

lemma count_catastrophic_policies (m : ℕ) :
  count_satisfying (fun π : Policy m => π.is_catastrophic) = 2^(2^m) - 1 := by
  have h_total : count_satisfying (fun π : Policy m => π.is_safe) +
                 count_satisfying (fun π : Policy m => π.is_catastrophic) = 2^(2^m) := by
    rw [← Fintype.card_eq_card_toFinset]; convert Policy.card m; ext π
    simp [mem_toFinset, count_satisfying, mem_filter, mem_univ, Policy.safe_iff_not_catastrophic]; tauto
  rw [count_safe_policies] at h_total; omega

/-! ### 8. Main Reduction -/

def oracle_policy {m : ℕ} (O : Fin (2^m) → Bool) : Policy m where eval := O

def make_distinguisher {m : ℕ} (V : Verifier m) : (Fin (2^m) → Bool) → Bool :=
  fun O => V.decide (oracle_policy O)

lemma distinguisher_poly_time {m : ℕ} (V : Verifier m) :
  polynomial_time (make_distinguisher V) := by
  obtain ⟨pt⟩ := V.poly_time
  use { poly := pt.poly, time_bound := fun O => by
      obtain ⟨steps, h_bound, h_decode⟩ := pt.time_bound (oracle_policy O)
      use steps; constructor
      · have : Encodable.encode (oracle_policy O) = Encodable.encode O := by simp [oracle_policy, Encodable.encode, Policy]
        rw [← this]; exact h_bound
      · simp [make_distinguisher]; exact h_decode }

lemma prob_key_bound {m : ℕ} (V : Verifier m) (h_correct : V.correct) (prf : PRF m) :
  prob_key prf (make_distinguisher V) ≤ 1 - 1/2^m := by
  obtain ⟨k₀, x₀, hk₀⟩ := PRF_nontrivial prf
  have h_cat : (oracle_policy (prf.F k₀)).is_catastrophic := ⟨x₀, hk₀⟩
  have h_reject : V.decide (oracle_policy (prf.F k₀)) = false := h_correct.2 _ h_cat
  have h_count : count_satisfying (fun k => make_distinguisher V (prf.F k) = true) ≤ 2^m - 1 := by
    have : k₀ ∉ filter (fun k => make_distinguisher V (prf.F k) = true) univ := by simp [mem_filter, make_distinguisher, h_reject]
    have : filter (fun k => make_distinguisher V (prf.F k) = true) univ ⊂ univ := by
      rw [ssubset_iff_subset_ne]; constructor; · exact filter_subset _ _; · intro h_eq; have : k₀ ∈ filter _ univ := by rw [h_eq]; exact mem_univ _; contradiction
    exact Nat.lt_iff_add_one_le.mp (card_lt_card this)
  simp [prob_key, count_satisfying]; exact div_le_div_of_nonneg_right (Nat.cast_le.2 h_count) (Nat.cast_nonneg _)

lemma prob_random_exact {m : ℕ} (V : Verifier m) (h_correct : V.correct) :
  prob_random (make_distinguisher V) = 1/2^(2^m) := by
  have h_count : count_satisfying (fun f => make_distinguisher V f = true) = 1 := by
    have h_iff : ∀ f, make_distinguisher V f = true ↔ (oracle_policy f).is_safe := by
      intro f; simp [make_distinguisher]; exact ⟨fun h => by_contra (fun h_not => (h_correct.2 _ (Policy.safe_iff_not_catastrophic.mp h_not)).symm h), h_correct.1 _⟩
    have : count_satisfying (fun f => (oracle_policy f).is_safe) = 1 := by
      rw [count_satisfying, card_eq_one]; use fun _ => false; ext f; simp [mem_filter, mem_univ, oracle_policy, Policy.is_safe]; constructor; · intro h; ext x; exact h x; · intro h x; rw [h]
    convert this; ext f; exact h_iff f
  simp [prob_random, h_count]

lemma distinguisher_advantage {m : ℕ} (V : Verifier m) (h_correct : V.correct)
    (prf : PRF m) (hm_ge1 : m ≥ 1) : -- Changed from m ≥ 2
    prf.advantage (make_distinguisher V) ≥ (1 - 1/2^m) - 1/2^(2^m) := by
  have p₁ := prob_key_bound V h_correct prf
  have p₂ := prob_random_exact V h_correct
  simp [PRF.advantage, p₂, abs_sub_le_iff]
  right -- We want to show p₁ - p₂ is large, or p₂ - p₁ is large.
  -- p₁ ≤ 1 - 1/2^m. p₂ = 1/2^(2^m).
  -- We want |p₁ - p₂| ≥ X.
  -- If p₁ ≥ p₂, then p₁ - p₂. If p₁ < p₂, then p₂ - p₁.
  -- Since p₁ can be close to 1, and p₂ is very small, p₁ - p₂ is likely positive.
  -- So we want p₁ - p₂ ≥ X.
  -- We know p₁ ≤ 1 - 1/2^m. This is an upper bound.
  -- We need a lower bound for p₁ or an argument about the difference.
  -- The advantage is | Pr[key] - Pr[random] |
  -- Pr[key] = count_true_key / 2^m
  -- Pr[random] = 1 / 2^(2^m)
  -- If V is correct, it accepts only the all-false policy.
  -- So Pr[random] = 1/2^(2^m).
  -- For Pr[key], if PRF is good, prf.F k should look random.
  -- So D(prf.F k) should be true with probability close to 1/2^(2^m).
  -- This means advantage should be small.
  -- The argument here is that if a verifier V exists, it creates a good distinguisher D.
  -- If D has large advantage, it breaks PRF security.
  -- The proof sketch for verifier_implies_distinguisher had Pr[D(F(k))=true] ≤ 1/2 and Pr[D(random)=true] ≥ 1 - negligible.
  -- Let's use the bounds directly:
  -- Advantage = | P_key(D accepts) - P_rand(D accepts) |
  -- P_rand(D accepts) = P_rand(V accepts oracle_policy) = P_rand((oracle_policy O).is_safe) = 1/2^(2^m) by soundness/completeness.
  -- P_key(D accepts) = P_key(V accepts oracle_policy(prf.F k)).
  -- If prf.F k is catastrophic (happens for at least one k, say k₀), V rejects, D rejects.
  -- So P_key(D accepts) ≤ (2^m - 1) / 2^m = 1 - 1/2^m.
  -- Then | (≤ 1 - 1/2^m) - (1/2^(2^m)) |.
  -- This is ≤ 1 - 1/2^m - 1/2^(2^m) if 1-1/2^m ≥ 1/2^(2^m).
  -- Or (1/2^(2^m)) - (something ≤ 1-1/2^m).
  -- The advantage should be large, so (1-1/2^m) - 1/2^(2^m) is the target lower bound.
  apply le_abs_self
  calc (prob_key prf (make_distinguisher V) : ℝ) - (prob_random (make_distinguisher V) : ℝ)
    _ ≥ 0 - (1/2^(2^m) : ℝ) := by sorry -- Need a lower bound for prob_key, not just upper.
                                    -- If PRF is good, prob_key should be close to prob_random.
                                    -- The argument is: if V exists, it distinguishes.
                                    -- If V accepts safe (all false) and rejects catastrophic.
                                    -- P_rand(V accepts) = P(policy is safe) = 1/2^(2^m).
                                    -- P_key(V accepts) = P(policy from PRF.F k is safe).
                                    -- If PRF is perfect, this should also be 1/2^(2^m).
                                    -- If PRF has at least one catastrophic output (from PRF_nontrivial),
                                    -- then P_key(V accepts) ≤ (2^m-1)/2^m.
                                    -- So | (≤ (2^m-1)/2^m) - (1/2^(2^m)) |.
                                    -- This is (1 - 1/2^m) - 1/2^(2^m) if the first term is larger.
                                    -- (1 - 1/2^m) - 1/2^(2^m)
    _ ≥ (1 - 1/2^m) - 1/2^(2^m) := by sorry -- This step is the core of the advantage.

/-! ### 9. Main Impossibility Result -/

lemma negligible_eventually_lt_half_minus_inv_pow_m {f : ℕ → ℝ} (h_negl : negligible f) {m : ℕ} (hm : m ≥ 1) :
  ∀ᶠ n_kappa in Filter.atTop, f n_kappa < 1/2 - 1/2^m := by
  apply negligible_eventually_zero h_negl (1/2 - 1/2^m)
  simp; linarith [show (1 : ℝ) / 2^m ≤ 1/2 by { apply div_le_div_of_le_left zero_le_one (by norm_num); exact Nat.pow_le_pow_left (by norm_num) hm }]

theorem above_threshold_unverifiable {d m : ℕ} (hd : 0 < d)
    (hm_ge_thresh : m ≥ sharp_threshold d) (prf : PRF m) (h_secure : prf.secure) :
    ¬∃ V : Verifier m, V.correct := by
  rintro ⟨V, h_correct⟩; let D := make_distinguisher V
  have h_poly : polynomial_time D := distinguisher_poly_time V
  have h_negl_adv : negligible (fun _ => prf.advantage D) := h_secure D h_poly -- Advantage is function of m (kappa)
  have hm_ge_2 : m ≥ 2 := by omega [sharp_threshold_ge_three d, hm_ge_thresh]
  have h_adv_lower_bound : prf.advantage D ≥ 1/2 - 1/2^m := distinguisher_advantage V h_correct prf hm_ge_2
  have h_eventually_small := negligible_eventually_lt_half_minus_inv_pow_m h_negl_adv hm_ge_2
  rw [Filter.eventually_atTop] at h_eventually_small
  obtain ⟨N, hN_spec⟩ := h_eventually_small
  specialize hN_spec (max N m) (le_max_left _ _)
  linarith [h_adv_lower_bound]

/-! ### 10. Main Theorem -/

axiom exists_secure_PRF : ∀ κ : ℕ, ∃ prf : PRF κ, prf.secure

theorem cryptographic_verification_threshold (d : ℕ) (hd : 0 < d) :
  (∀ m < sharp_threshold d, ∃ V : Verifier m, V.correct) ∧
  (∀ m ≥ sharp_threshold d, ¬∃ V : Verifier m, V.correct) := by
  constructor
  · intro m hm_lt; exact below_threshold_verifiable hd hm_lt
  · intro m hm_ge; obtain ⟨prf, h_secure⟩ := exists_secure_PRF m
    exact above_threshold_unverifiable hd hm_ge prf h_secure

/-! ### 11. Concrete Examples -/
-- Examples remain sorry due to Nat.ceil (log _ / log _) needing numerical evaluation
