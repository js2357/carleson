import Carleson.WeakType

noncomputable section

open NNReal ENNReal NormedSpace MeasureTheory Set

variable {α α' E E₁ E₂ E₃ : Type*} {m : MeasurableSpace α} {m : MeasurableSpace α'}
  {p p' q : ℝ≥0∞} {c : ℝ≥0}
  {μ : Measure α} {ν : Measure α'}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
  [NormedAddCommGroup E₂] [NormedSpace ℝ E₂] [FiniteDimensional ℝ E₂]
  [NormedAddCommGroup E₃] [NormedSpace ℝ E₃] [FiniteDimensional ℝ E₃]
  [MeasurableSpace E] [BorelSpace E]
  [MeasurableSpace E₁] [BorelSpace E₁]
  [MeasurableSpace E₂] [BorelSpace E₂]
  [MeasurableSpace E₃] [BorelSpace E₃]
  (L : E₁ →L[ℝ] E₂ →L[ℝ] E₃)
  {f g : α → E} {t : ℝ} {s x y : ℝ≥0∞}
  {T : (α → E₁) → (α' → E₂)}


namespace MeasureTheory

/-- The `t`-truncation of a function `f`. -/
def trunc (f : α → E) (t : ℝ) (x : α) : E := if ‖f x‖ ≤ t then f x else 0

lemma aestronglyMeasurable_trunc (hf : AEStronglyMeasurable f μ) :
    AEStronglyMeasurable (trunc f t) μ := sorry

-- /-- The `t`-truncation of `f : α →ₘ[μ] E`. -/
-- def AEEqFun.trunc (f : α →ₘ[μ] E) (t : ℝ) : α →ₘ[μ] E :=
--   AEEqFun.mk (MeasureTheory.trunc f t) (aestronglyMeasurable_trunc f.aestronglyMeasurable)

-- /-- A set of measurable functions is closed under truncation. -/
-- class IsClosedUnderTruncation (U : Set (α →ₘ[μ] E)) : Prop where
--   trunc_mem {f : α →ₘ[μ] E} (hf : f ∈ U) (t : ℝ) : f.trunc t ∈ U

/-- The operator is subadditive on functions satisfying `P` with constant `A`. -/
def SubadditiveOn (T : (α → E₁) → α' → E₂) (P : (α → E₁) → Prop) (A : ℝ) : Prop :=
  ∀ (f g : α → E₁) (x : α'), P f → P g → ‖T (f + g) x‖ ≤ A * (‖T f x‖ + ‖T g x‖)

namespace SubadditiveOn

def antitone {T : (α → E₁) → α' → E₂} {P P' : (α → E₁) → Prop}
    (h : ∀ {u : α → E₁}, P u → P' u) {A : ℝ} (sa : SubadditiveOn T P' A) : SubadditiveOn T P A :=
  fun f g x hf hg ↦ sa f g x (h hf) (h hg)

lemma neg (P : (α → E₁) → Prop) {A : ℝ} (hA : A < 0) (h : SubadditiveOn T P A)
  (f : α → E₁) (hf : P f) : T f = 0 :=
  funext fun x ↦ norm_le_zero_iff.mp (by nlinarith [norm_nonneg (T (f + f) x), h f f x hf hf])

lemma zero {P : (α → E₁) → Prop} (hP : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (A : ℝ) (h : ∀ u, P u → T u = 0) : SubadditiveOn T P A :=
  fun f g x hf hg ↦ by simp [h f hf, h g hg, h (f + g) (hP hf hg)]

lemma biSup {ι : Type*} (𝓑 : Set ι) {T : ι → (α → E₁) → α' → ℝ≥0∞}
    {P : (α → E₁) → Prop} (hT : ∀ (u : α → E₁) (x : α'), P u → ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (hP : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (A : ℝ) (h : ∀ i ∈ 𝓑, SubadditiveOn (fun u x ↦ (T i u x).toReal) P A) :
    SubadditiveOn (fun u x ↦ (⨆ i ∈ 𝓑, T i u x).toReal) P A := by
  have hT' : ∀ i ∈ 𝓑, ∀ (x : α') (u : α → E₁), P u → T i u x ≠ ∞ :=
    fun i hi x f hf h ↦ hT f x hf <| eq_top_iff.mpr <| h ▸ le_biSup (fun i ↦ T i f x) hi
  by_cases A0 : A < 0
  · refine SubadditiveOn.zero hP A (fun f hf ↦ funext fun x ↦ ?_)
    suffices ⨆ i ∈ 𝓑, T i f x = 0 by simp [this]
    simp only [iSup_eq_zero]
    intro i hi
    have := (toReal_eq_zero_iff _).mp (congr_fun ((h i hi).neg P A0 f hf) x)
    exact this.resolve_right (hT' i hi x f hf)
  push_neg at A0
  intro f g x hf hg
  simp only [Real.norm_eq_abs, abs_toReal]
  refine le_trans ?_ <| mul_le_mul_of_nonneg_left
    (toReal_le_add' (le_refl _) (fun h ↦ by simp [h]) (fun h ↦ by simp [h])) A0
  rw [← toReal_ofReal A0, ← toReal_mul]
  apply toReal_mono <| mul_ne_top ofReal_ne_top (add_ne_top.mpr ⟨hT f x hf, hT g x hg⟩)
  simp only [iSup_le_iff]
  intro i hi
  specialize h i hi f g x hf hg
  simp only [Real.norm_eq_abs, abs_toReal] at h
  rw [← toReal_add (hT' i hi x f hf) (hT' i hi x g hg), ← toReal_ofReal A0, ← toReal_mul,
    toReal_le_toReal (hT' i hi x (f + g) (hP hf hg)) <| mul_ne_top ofReal_ne_top <|
    add_ne_top.mpr ⟨hT' i hi x f hf, hT' i hi x g hg⟩] at h
  apply h.trans
  gcongr <;> apply le_biSup _ hi

lemma indicator {T : (α → E₁) → α' → E₂} {P : (α → E₁) → Prop} {A : ℝ}
    (sa : SubadditiveOn T P A) (S : Set α') :
    SubadditiveOn (fun u x ↦ (S.indicator (fun y ↦ T u y) x)) P A := by
  intro f g x hf hg
  by_cases hx : x ∈ S <;> simp [hx, sa f g x hf hg]

-- If `T` is constant in the second argument (but not necessarily the first) and satisfies
-- a subadditivity criterion, then `SubadditiveOn T P 1`
lemma const (t : (α → E₁) → E₂) (P : (α → E₁) → Prop)
    (h_add : ∀ {f g}, P f → P g → ‖t (f + g)‖ ≤ ‖t f‖ + ‖t g‖) :
    SubadditiveOn (fun u (_ : α') ↦ t u) P 1 := by
  intro f g x hf hg
  simpa using h_add hf hg

end SubadditiveOn

/-- The operator is sublinear on functions satisfying `P` with constant `A`. -/
def SublinearOn (T : (α → E₁) → α' → E₂) (P : (α → E₁) → Prop) (A : ℝ) : Prop :=
  SubadditiveOn T P A ∧ ∀ (f : α → E₁) (c : ℝ), P f → c ≥ 0 → T (c • f) = c • T f

namespace SublinearOn

lemma antitone {T : (α → E₁) → α' → E₂} {P P' : (α → E₁) → Prop}
    (h : ∀ {u : α → E₁}, P u → P' u) {A : ℝ} (sl : SublinearOn T P' A) : SublinearOn T P A :=
  ⟨sl.1.antitone (fun hu ↦ h hu), fun u c hu hc ↦ sl.2 u c (h hu) hc⟩

lemma biSup {ι : Type*} (𝓑 : Set ι) (T : ι → (α → E₁) → α' → ℝ≥0∞)
    {P : (α → E₁) → Prop} (hT : ∀ (u : α → E₁) (x : α'), P u → ⨆ i ∈ 𝓑, T i u x ≠ ∞)
    (h_add : ∀ {f g : α → E₁}, P f → P g → P (f + g))
    (h_smul : ∀ {f : α → E₁} {c : ℝ}, P f → c ≥ 0 → P (c • f))
    {A : ℝ} (h : ∀ i ∈ 𝓑, SublinearOn (fun u x ↦ (T i u x).toReal) P A) :
    SublinearOn (fun u x ↦ (⨆ i ∈ 𝓑, T i u x).toReal) P A := by
  have hT' : ∀ i ∈ 𝓑, ∀ (x : α') (u : α → E₁), P u → T i u x ≠ ∞ :=
    fun i hi x f hf h ↦ hT f x hf <| eq_top_iff.mpr <| h ▸ le_biSup (fun i ↦ T i f x) hi
  refine ⟨SubadditiveOn.biSup 𝓑 hT h_add A (fun i hi ↦ (h i hi).1), ?_⟩
  intro f c hf hc
  ext x
  rw [Pi.smul_apply, ← ENNReal.toReal_ofReal hc, smul_eq_mul]
  simp only [← toReal_mul, ENNReal.mul_iSup]
  congr 1
  refine biSup_congr (fun i hi ↦ ?_)
  have := congr_fun ((h i hi).2 f c hf hc) x
  simp only [Pi.smul_apply, smul_eq_mul, ← toReal_ofReal_mul c (T i f x) hc] at this
  rw [ENNReal.toReal_eq_toReal (hT' i hi x (c • f) (h_smul hf hc))
    (mul_lt_top ofReal_ne_top (hT' i hi x f hf)).ne] at this
  rwa [toReal_ofReal hc]

lemma indicator {T : (α → E₁) → α' → E₂} {P : (α → E₁) → Prop} {A : ℝ} (S : Set α')
    (sl : SublinearOn T P A) :
    SublinearOn (fun u x ↦ (S.indicator (fun y ↦ T u y) x)) P A := by
  refine ⟨SubadditiveOn.indicator sl.1 S, fun f c hf hc ↦ funext (fun x ↦ ?_)⟩
  by_cases hx : x ∈ S <;> simp [hx, congr_fun (sl.2 f c hf hc) x]

-- If `T` is constant in the second argument (but not necessarily the first) and satisfies
-- certain requirements, then `SublinearOn T P 1`
lemma const (t : (α → E₁) → E₂) (P : (α → E₁) → Prop)
    (h_add : ∀ {f g}, P f → P g → ‖t (f + g)‖ ≤ ‖t f‖ + ‖t g‖)
    (h_smul : ∀ f {c : ℝ}, P f → c ≥ 0 → t (c • f) = c • t f) :
    SublinearOn (fun u (_ : α') ↦ t u) P 1 := by
  refine ⟨SubadditiveOn.const t P h_add, fun f c hf hc ↦ funext (fun x ↦ ?_)⟩
  simpa using h_smul f hf hc

end SublinearOn

/-- The constant occurring in the real interpolation theorem. -/
-- todo: remove unused variables
def C_realInterpolation (p₀ p₁ q₀ q₁ p q : ℝ≥0∞) (C₀ C₁ t A : ℝ≥0) : ℝ≥0 := sorry

-- todo: add necessary hypotheses
lemma C_realInterpolation_pos (p₀ p₁ q₀ q₁ p q : ℝ≥0∞) (C₀ C₁ t A : ℝ≥0) :
    0 < C_realInterpolation p₀ p₁ q₀ q₁ p q C₀ C₁ t := sorry

/-- Marcinkiewicz real interpolation theorem. -/
-- feel free to assume that T also respect a.e.-equality if needed.
/- For the proof, see
Folland, Real Analysis. Modern Techniques and Their Applications, section 6.4, theorem 6.28.
You want to use `trunc f A` when the book uses `h_A`.
Minkowski's inequality is `ENNReal.lintegral_Lp_add_le` -/
theorem exists_hasStrongType_real_interpolation {p₀ p₁ q₀ q₁ p q : ℝ≥0∞}
    (hp₀ : p₀ ∈ Icc 1 q₀) (hp₁ : p₁ ∈ Icc 1 q₁) (hq : q₀ ≠ q₁)
    {C₀ C₁ t A : ℝ≥0} (ht : t ∈ Ioo 0 1) (hC₀ : 0 < C₀) (hC₁ : 0 < C₁)
    (hp : p⁻¹ = (1 - t) / p₀ + t / p₁) (hq : q⁻¹ = (1 - t) / q₀ + t / q₁)
    (hmT : ∀ f, Memℒp f p₀ μ ∨ Memℒp f p₁ μ → AEStronglyMeasurable (T f) ν)
    (hT : SublinearOn T (fun f ↦ Memℒp f p₀ μ ∨ Memℒp f p₁ μ) A)
    (h₀T : HasWeakType T p₀ q₀ μ ν C₀) (h₁T : HasWeakType T p₁ q₁ μ ν C₁) :
    HasStrongType T p p μ ν (C_realInterpolation p₀ p₁ q₀ q₁ p q C₀ C₁ t A) := sorry

/- State and prove Remark 1.2.7 -/

end MeasureTheory
