import Mathlib.Probability.Moments.Variance
import Mathlib.Probability.Independence.Basic
import Mathlib.Tactic

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace WassersteinSubadditivity

/-- A coupling of two real laws with finite second moments. -/
structure Coupling (μ ν : Measure ℝ) where
  measure : Measure (ℝ × ℝ)
  probability : IsProbabilityMeasure measure
  fst_map : measure.map Prod.fst = μ
  snd_map : measure.map Prod.snd = ν
  fst_L2 : MemLp Prod.fst 2 measure
  snd_L2 : MemLp Prod.snd 2 measure

attribute [instance] Coupling.probability

/-- Every probability coupling of P₂ marginals belongs to `Coupling`. -/
def couplingOfMarginals {μ ν : Measure ℝ} (ρ : Measure (ℝ × ℝ))
    [IsProbabilityMeasure ρ] (hfst : ρ.map Prod.fst = μ) (hsnd : ρ.map Prod.snd = ν)
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun x : ℝ => x) 2 ν) :
    Coupling μ ν where
  measure := ρ
  probability := inferInstance
  fst_map := hfst
  snd_map := hsnd
  fst_L2 := hμ.comp_measurePreserving ⟨measurable_fst, hfst⟩
  snd_L2 := hν.comp_measurePreserving ⟨measurable_snd, hsnd⟩

/-- Quadratic transport cost. -/
def Coupling.cost {μ ν : Measure ℝ} (π : Coupling μ ν) : ℝ :=
  ∫ p, (p.1 - p.2) ^ 2 ∂π.measure

/-- The square of the 2-Wasserstein distance, on probability laws in P₂(ℝ). -/
def w₂sq (μ ν : Measure ℝ) : ℝ :=
  sInf (Set.range (fun π : Coupling μ ν => π.cost))

lemma cost_nonneg {μ ν : Measure ℝ} (π : Coupling μ ν) : 0 ≤ π.cost :=
  integral_nonneg fun _ => sq_nonneg _

lemma costs_bddBelow (μ ν : Measure ℝ) :
    BddBelow (Set.range (fun π : Coupling μ ν => π.cost)) :=
  ⟨0, by rintro _ ⟨π, rfl⟩; exact cost_nonneg π⟩

lemma w₂sq_le_cost {μ ν : Measure ℝ} (π : Coupling μ ν) : w₂sq μ ν ≤ π.cost :=
  csInf_le (costs_bddBelow μ ν) ⟨π, rfl⟩

def independentCoupling (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun x : ℝ => x) 2 ν) :
    Coupling μ ν where
  measure := μ.prod ν
  probability := inferInstance
  fst_map := by simp
  snd_map := by simp
  fst_L2 := hμ.comp_measurePreserving measurePreserving_fst
  snd_L2 := hν.comp_measurePreserving measurePreserving_snd

lemma w₂sq_nonneg (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun x : ℝ => x) 2 ν) :
    0 ≤ w₂sq μ ν := by
  unfold w₂sq
  apply le_csInf (s := Set.range (fun π : Coupling μ ν => π.cost))
    ⟨_, ⟨independentCoupling μ ν hμ hν, rfl⟩⟩
  rintro _ ⟨π, rfl⟩
  exact cost_nonneg π

lemma exists_cost_lt (μ ν : Measure ℝ) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (hμ : MemLp (fun x : ℝ => x) 2 μ) (hν : MemLp (fun x : ℝ => x) 2 ν)
    {ε : ℝ} (hε : 0 < ε) : ∃ π : Coupling μ ν, π.cost < w₂sq μ ν + ε := by
  have hn : (Set.range (fun π : Coupling μ ν => π.cost)).Nonempty :=
    ⟨_, ⟨independentCoupling μ ν hμ hν, rfl⟩⟩
  obtain ⟨_, ⟨π, rfl⟩, hπ⟩ := exists_lt_of_csInf_lt hn (lt_add_of_pos_right _ hε)
  exact ⟨π, hπ⟩

variable {ι : Type*} [Fintype ι]

/-- Law of a linear combination of independent variables with prescribed laws. -/
def linearLaw (α : ι → ℝ) (μ : ι → Measure ℝ) : Measure ℝ :=
  (Measure.pi μ).map (fun x => ∑ i, α i * x i)

lemma measurable_linear (α : ι → ℝ) : Measurable (fun x : ι → ℝ => ∑ i, α i * x i) := by
  fun_prop

lemma coupling_mean_sub {μ ν : Measure ℝ} (π : Coupling μ ν)
    (hμ : ∫ x, x ∂μ = 0) (hν : ∫ x, x ∂ν = 0) :
    ∫ p, (p.1 - p.2) ∂π.measure = 0 := by
  rw [integral_sub (π.fst_L2.integrable (by norm_num))
    (π.snd_L2.integrable (by norm_num))]
  have hf : ∫ p, p.1 ∂π.measure = ∫ x, x ∂μ := by
    simpa only [π.fst_map] using
      (integral_map (μ := π.measure) measurable_fst.aemeasurable
        (f := fun x : ℝ => x) (by fun_prop)).symm
  have hs : ∫ p, p.2 ∂π.measure = ∫ x, x ∂ν := by
    simpa only [π.snd_map] using
      (integral_map (μ := π.measure) measurable_snd.aemeasurable
        (f := fun x : ℝ => x) (by fun_prop)).symm
  rw [hf, hs, hμ, hν, sub_self]

lemma product_cost (α : ι → ℝ) {μ ν : ι → Measure ℝ} (π : ∀ i, Coupling (μ i) (ν i))
    (hμ : ∀ i, ∫ x, x ∂μ i = 0) (hν : ∀ i, ∫ x, x ∂ν i = 0) :
    (∫ p : ι → ℝ × ℝ, (∑ i, α i * ((p i).1 - (p i).2)) ^ 2
      ∂Measure.pi (fun i => (π i).measure)) = ∑ i, (α i)^2 * (π i).cost := by
  let X : ι → (ℝ × ℝ) → ℝ := fun i p => α i * (p.1 - p.2)
  have hX : ∀ i, MemLp (X i) 2 (π i).measure := fun i =>
    ((π i).fst_L2.sub (π i).snd_L2).const_mul (α i)
  have hmean : ∀ i, ∫ p, X i p ∂(π i).measure = 0 := by
    intro i
    dsimp [X]
    rw [integral_const_mul, coupling_mean_sub (π i) (hμ i) (hν i), mul_zero]
  have hsumL2 : MemLp (fun p : ι → ℝ × ℝ => ∑ i, X i (p i)) 2
      (Measure.pi fun i => (π i).measure) := by
    exact memLp_finsetSum _ (fun i _ => (hX i).comp_measurePreserving
      (measurePreserving_eval (fun i => (π i).measure) i))
  have hmean_sum : (∫ p : ι → ℝ × ℝ, ∑ i, X i (p i)
      ∂Measure.pi (fun i => (π i).measure)) = 0 := by
    rw [integral_finsetSum (f := fun i (p : ι → ℝ × ℝ) => X i (p i)) Finset.univ (fun i _ => ((hX i).comp_measurePreserving
      (measurePreserving_eval (fun i => (π i).measure) i)).integrable (by norm_num))]
    apply Finset.sum_eq_zero
    intro i _
    change ∫ p, (X i ∘ Function.eval i) p ∂Measure.pi (fun i => (π i).measure) = 0
    have hm := (measurePreserving_eval (fun i => (π i).measure) i).map_eq
    have ht : (∫ p, X i p ∂(Measure.pi (fun i => (π i).measure)).map (Function.eval i)) = 0 := by
      rw [hm]
      exact hmean i
    rw [integral_map (measurable_pi_apply i).aemeasurable (by fun_prop)] at ht
    exact ht
  have hv := variance_sum_pi hX
  have hfun : (∑ i, fun p : ι → ℝ × ℝ => X i (p i)) = (fun p => ∑ i, X i (p i)) := by
    funext p
    simp only [Finset.sum_apply]
  rw [hfun] at hv
  rw [variance_eq_integral hsumL2.aemeasurable] at hv
  simp only [hmean_sum, sub_zero] at hv
  calc
    _ = ∑ i, variance (X i) (π i).measure := hv
    _ = ∑ i, (α i)^2 * (π i).cost := by
      apply Finset.sum_congr rfl
      intro i _
      rw [variance_eq_integral (hX i).aemeasurable, hmean i]
      simp only [sub_zero, X, mul_pow, Coupling.cost]
      exact integral_const_mul _ _

variable {Ω : Type*} [MeasurableSpace Ω]

def couplingOfMaps (ρ : Measure Ω) [IsProbabilityMeasure ρ] (S Z : Ω → ℝ)
    (hS : Measurable S) (hZ : Measurable Z) (hS2 : MemLp S 2 ρ) (hZ2 : MemLp Z 2 ρ) :
    Coupling (ρ.map S) (ρ.map Z) where
  measure := ρ.map (fun ω => (S ω, Z ω))
  probability := inferInstance
  fst_map := by rw [Measure.map_map measurable_fst (hS.prodMk hZ)]; rfl
  snd_map := by rw [Measure.map_map measurable_snd (hS.prodMk hZ)]; rfl
  fst_L2 := (memLp_map_measure_iff (by fun_prop) (hS.prodMk hZ).aemeasurable).2 hS2
  snd_L2 := (memLp_map_measure_iff (by fun_prop) (hS.prodMk hZ).aemeasurable).2 hZ2

lemma couplingOfMaps_cost (ρ : Measure Ω) [IsProbabilityMeasure ρ] (S Z : Ω → ℝ)
    (hS : Measurable S) (hZ : Measurable Z) (hS2 : MemLp S 2 ρ) (hZ2 : MemLp Z 2 ρ) :
    (couplingOfMaps ρ S Z hS hZ hS2 hZ2).cost = ∫ ω, (S ω - Z ω)^2 ∂ρ := by
  exact integral_map (hS.prodMk hZ).aemeasurable (by fun_prop)

lemma map_product_fst (α : ι → ℝ) {μ ν : ι → Measure ℝ}
    (π : ∀ i, Coupling (μ i) (ν i)) :
    (Measure.pi (fun i => (π i).measure)).map (fun p => ∑ i, α i * (p i).1) =
      linearLaw α μ := by
  have hm : (Measure.pi (fun i => (π i).measure)).map (fun p i => (p i).1) =
      Measure.pi μ := by
    simpa only [Coupling.fst_map] using
      (Measure.pi_map_pi (μ := fun i => (π i).measure)
        (f := fun _ => Prod.fst) (fun _ => measurable_fst.aemeasurable))
  calc
    _ = ((Measure.pi (fun i => (π i).measure)).map (fun p i => (p i).1)).map
        (fun x => ∑ i, α i * x i) := by
      rw [Measure.map_map (measurable_linear α) (by fun_prop)]
      rfl
    _ = _ := by rw [hm]; rfl

lemma map_product_snd (α : ι → ℝ) {μ ν : ι → Measure ℝ}
    (π : ∀ i, Coupling (μ i) (ν i)) :
    (Measure.pi (fun i => (π i).measure)).map (fun p => ∑ i, α i * (p i).2) =
      linearLaw α ν := by
  have hm : (Measure.pi (fun i => (π i).measure)).map (fun p i => (p i).2) =
      Measure.pi ν := by
    simpa only [Coupling.snd_map] using
      (Measure.pi_map_pi (μ := fun i => (π i).measure)
        (f := fun _ => Prod.snd) (fun _ => measurable_snd.aemeasurable))
  calc
    _ = ((Measure.pi (fun i => (π i).measure)).map (fun p i => (p i).2)).map
        (fun x => ∑ i, α i * x i) := by
      rw [Measure.map_map (measurable_linear α) (by fun_prop)]
      rfl
    _ = _ := by rw [hm]; rfl

lemma w₂sq_linearLaw_le_costs (α : ι → ℝ) {μ ν : ι → Measure ℝ}
    (π : ∀ i, Coupling (μ i) (ν i))
    (hμ : ∀ i, ∫ x, x ∂μ i = 0) (hν : ∀ i, ∫ x, x ∂ν i = 0) :
    w₂sq (linearLaw α μ) (linearLaw α ν) ≤ ∑ i, (α i)^2 * (π i).cost := by
  let ρ := Measure.pi (fun i => (π i).measure)
  let S : (ι → ℝ × ℝ) → ℝ := fun p => ∑ i, α i * (p i).1
  let Z : (ι → ℝ × ℝ) → ℝ := fun p => ∑ i, α i * (p i).2
  have hS : Measurable S := by dsimp [S]; fun_prop
  have hZ : Measurable Z := by dsimp [Z]; fun_prop
  have hS2 : MemLp S 2 ρ := memLp_finsetSum _ fun i _ =>
    ((π i).fst_L2.comp_measurePreserving
      (measurePreserving_eval (fun i => (π i).measure) i)).const_mul (α i)
  have hZ2 : MemLp Z 2 ρ := memLp_finsetSum _ fun i _ =>
    ((π i).snd_L2.comp_measurePreserving
      (measurePreserving_eval (fun i => (π i).measure) i)).const_mul (α i)
  have hb := w₂sq_le_cost (couplingOfMaps ρ S Z hS hZ hS2 hZ2)
  rw [couplingOfMaps_cost] at hb
  change w₂sq (ρ.map S) (ρ.map Z) ≤ _ at hb
  rw [map_product_fst α π, map_product_snd α π] at hb
  convert hb using 1
  rw [← product_cost α π hμ hν]
  congr 1
  funext p
  dsimp [S, Z]
  rw [← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Wasserstein subadditivity for centered probability laws. -/
theorem wasserstein_linear_combination (α : ι → ℝ) (μ ν : ι → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ i, IsProbabilityMeasure (ν i)]
    (hμ2 : ∀ i, MemLp (fun x : ℝ => x) 2 (μ i))
    (hν2 : ∀ i, MemLp (fun x : ℝ => x) 2 (ν i))
    (hμ0 : ∀ i, ∫ x, x ∂μ i = 0) (hν0 : ∀ i, ∫ x, x ∂ν i = 0) :
    w₂sq (linearLaw α μ) (linearLaw α ν) ≤ ∑ i, (α i)^2 * w₂sq (μ i) (ν i) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  let A : ℝ := ∑ i, (α i)^2
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => sq_nonneg (α i)
  let δ := ε / (A + 1)
  have hδ : 0 < δ := div_pos hε (by linarith)
  choose π hπ using fun i => exists_cost_lt (μ i) (ν i) (hμ2 i) (hν2 i) hδ
  calc
    _ ≤ ∑ i, (α i)^2 * (π i).cost := w₂sq_linearLaw_le_costs α π hμ0 hν0
    _ ≤ ∑ i, (α i)^2 * (w₂sq (μ i) (ν i) + δ) :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hπ i).le (sq_nonneg _)
    _ = (∑ i, (α i)^2 * w₂sq (μ i) (ν i)) + A * δ := by
      simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, A]
    _ ≤ (∑ i, (α i)^2 * w₂sq (μ i) (ν i)) + ε := by
      have heq : δ * (A + 1) = ε := div_mul_cancel₀ ε (by linarith : A + 1 ≠ 0)
      nlinarith

lemma law_sum_of_independent (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (α : ι → ℝ) (S : ι → Ω → ℝ) (hS : ∀ i, Measurable (S i))
    (hind : iIndepFun S ρ) :
    ρ.map (fun ω => ∑ i, α i * S i ω) = linearLaw α (fun i => ρ.map (S i)) := by
  unfold linearLaw
  rw [← hind.map_fun_eq_pi_map (fun i => (hS i).aemeasurable),
    Measure.map_map (measurable_linear α) (by fun_prop)]
  rfl

/-- The random-variable form of the lemma, with independence within each family. -/
theorem wasserstein_linear_combination_randomVariables
    (ρ : Measure Ω) [IsProbabilityMeasure ρ] (α : ι → ℝ) (S Z : ι → Ω → ℝ)
    (hS : ∀ i, Measurable (S i)) (hZ : ∀ i, Measurable (Z i))
    (hS2 : ∀ i, MemLp (S i) 2 ρ) (hZ2 : ∀ i, MemLp (Z i) 2 ρ)
    (hS0 : ∀ i, ∫ ω, S i ω ∂ρ = 0) (hZ0 : ∀ i, ∫ ω, Z i ω ∂ρ = 0)
    (hindS : iIndepFun S ρ) (hindZ : iIndepFun Z ρ) :
    w₂sq (ρ.map (fun ω => ∑ i, α i * S i ω))
      (ρ.map (fun ω => ∑ i, α i * Z i ω)) ≤
        ∑ i, (α i)^2 * w₂sq (ρ.map (S i)) (ρ.map (Z i)) := by
  rw [law_sum_of_independent ρ α S hS hindS, law_sum_of_independent ρ α Z hZ hindZ]
  apply wasserstein_linear_combination
  · intro i
    exact (memLp_map_measure_iff (by fun_prop) (hS i).aemeasurable).2 (hS2 i)
  · intro i
    exact (memLp_map_measure_iff (by fun_prop) (hZ i).aemeasurable).2 (hZ2 i)
  · intro i
    rw [integral_map (hS i).aemeasurable (by fun_prop)]
    exact hS0 i
  · intro i
    rw [integral_map (hZ i).aemeasurable (by fun_prop)]
    exact hZ0 i

#print axioms wasserstein_linear_combination_randomVariables

end WassersteinSubadditivity
