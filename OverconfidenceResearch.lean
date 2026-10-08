import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.Continuous
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Convex.Mul

/-!
# Overestimation / Overplacement / Overprecision

合并阅读版，由 scripts/assemble.py 从六个模块自动生成。
Lean 4.33.1；固定 Mathlib 版本见 lakefile.toml。
公式索引：D/O/T（基础），E（绝对高估），L（相对高估），P（精确度），H（下偏矩），C（反例）。
可直接在匹配的 Mathlib 项目中检查此文件；不要与 Overconfidence 项目入口同时导入。
数学定义、建模限制及验证记录见 README.md。
-/

/-! ## Source module: Overconfidence/Basic.lean -/
/-!
# 三种过度自信：共同的概率与随机序基础

约定：数值越大代表表现越好；`FSD P X Y` 表示 Y 一阶随机占优 X。
所有期望都是 Mathlib 的 Bochner 积分，概率来自真正的 Measure / ProbabilityMeasure。
定义中的可积性条件防止把不可积函数的形式积分当作期望使用。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace Overconfidence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- [D1] E_P[X] = ∫ X dP。调用时须具有可积性。 -/
def mean (P : Measure Ω) (X : Ω → ℝ) : ℝ := ∫ ω, X ω ∂P

/-- [D2] Var_P(X) = E_P[(X − E_P[X])²]。 -/
def variance (P : Measure Ω) (X : Ω → ℝ) : ℝ :=
  ∫ ω, (X ω - mean P X) ^ 2 ∂P

/-- [D3] 均值意义的 overestimation：主观平均表现严格高于基准。 -/
def Overestimation (P : Measure Ω) (X belief : Ω → ℝ) : Prop :=
  Integrable X P ∧ Integrable belief P ∧ mean P X < mean P belief

/-- [D4] 相对表现 R = X − B；B 是参照人/群体的表现，允许与 X 相关。 -/
def relative (X B : Ω → ℝ) : Ω → ℝ := fun ω => X ω - B ω

/-- [D5] 差值意义的 overplacement：高估自己相对参照者的平均表现。
这不等同于百分位排名；排名版本在 Placement 模块单独处理。 -/
def Overplacement (P : Measure Ω) (X B selfBelief otherBelief : Ω → ℝ) : Prop :=
  Overestimation P (relative X B) (relative selfBelief otherBelief)

/-- [D6] 方差意义的纯 overprecision：保持均值而严格低估离散程度。
这是明确选定的分布模型，不声称穷尽置信区间覆盖率等心理学测量定义。 -/
def Overprecision (P : Measure Ω) (X belief : Ω → ℝ) : Prop :=
  Integrable X P ∧ Integrable belief P ∧
  Integrable (fun ω => (X ω - mean P X) ^ 2) P ∧
  Integrable (fun ω => (belief ω - mean P belief) ^ 2) P ∧
  mean P belief = mean P X ∧ variance P belief < variance P X

/-- [O1] F_X(t) = P{X ≤ t}，取值 ℝ≥0∞（概率时自动属于 [0,1]）。 -/
def cdf (P : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ≥0∞ :=
  P (X ⁻¹' Iic t)

/-- [O2] X ≤st Y ⇔ ∀t, F_Y(t) ≤ F_X(t)。 -/
def FSD (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  ∀ t, cdf P Y t ≤ cdf P X t

/-- [O3] 期望效用生成的随机序：只测试两端均可积的效用。 -/
def UtilityLE (P : Measure Ω) (tests : (ℝ → ℝ) → Prop) (X Y : Ω → ℝ) : Prop :=
  ∀ u, tests u → Integrable (u ∘ X) P → Integrable (u ∘ Y) P →
    (∫ ω, u (X ω) ∂P) ≤ ∫ ω, u (Y ω) ∂P

/-- [O4] 二阶随机占优的递增凹效用定义：X ≤icv Y。 -/
def SSD (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  UtilityLE P (fun u => Monotone u ∧ ConcaveOn ℝ univ u) X Y

/-- [O5] 凸序：X ≤cx Y；方向代表 Y 更分散，而不是 Y 对风险厌恶者更好。 -/
def ConvexLE (P : Measure Ω) (X Y : Ω → ℝ) : Prop :=
  UtilityLE P (fun u => ConvexOn ℝ univ u) X Y

/-- [T1] 有序耦合技巧：X ≤ Y 几乎处处 ⇒ F_Y ≤ F_X。
参考原文件末尾 ae_le_implies_randomVariableStochLE 的真实测度版本。 -/
theorem fsd_of_ae_le (P : Measure Ω) {X Y : Ω → ℝ} (h : X ≤ᵐ[P] Y) :
    FSD P X Y := by
  intro t
  apply measure_mono_ae
  filter_upwards [h] with ω hω
  exact fun hy => le_trans hω hy

/-- [T2] 同一有序耦合同时比较所有可积递增效用。 -/
theorem utilityLE_of_ae_le (P : Measure Ω) {X Y : Ω → ℝ} (h : X ≤ᵐ[P] Y) :
    UtilityLE P Monotone X Y := by
  intro u hu hX hY
  apply integral_mono_ae hX hY
  filter_upwards [h] with ω hω
  exact hu hω

/-- [T3] 有序耦合 ⇒ SSD（从效用直接证明，不假定 CDF/效用等价定理）。 -/
theorem ssd_of_ae_le (P : Measure Ω) {X Y : Ω → ℝ} (h : X ≤ᵐ[P] Y) :
    SSD P X Y := by
  intro u hu hX hY
  exact utilityLE_of_ae_le P h u hu.1 hX hY

/-- [T4] 映射后仍是概率分布；可测性是实际输入条件。 -/
def law (P : ProbabilityMeasure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X (P : Measure Ω)) : ProbabilityMeasure ℝ := P.map hX

/-- [T5] 随机变量 CDF 等于其推前分布对 (−∞,t] 的质量。 -/
theorem law_cdf (P : ProbabilityMeasure Ω) (X : Ω → ℝ)
    (hX : AEMeasurable X (P : Measure Ω)) (t : ℝ) :
    (law P X hX : Measure ℝ) (Iic t) = cdf (P : Measure Ω) X t := by
  exact Measure.map_apply_of_aemeasurable hX measurableSet_Iic

/-- [T6] FSD 比较的确是在比较两个概率分布。 -/
theorem fsd_iff_law_cdf (P : ProbabilityMeasure Ω) (X Y : Ω → ℝ)
    (hX : AEMeasurable X (P : Measure Ω)) (hY : AEMeasurable Y (P : Measure Ω)) :
    FSD (P : Measure Ω) X Y ↔
      ∀ t, (law P Y hY : Measure ℝ) (Iic t) ≤ (law P X hX : Measure ℝ) (Iic t) := by
  simp only [law_cdf, FSD]

end Overconfidence

end -- close the source file noncomputable section

/-! ## Source module: Overconfidence/Estimation.lean -/
/-!
# Overestimation：定义、位置平移模型与一阶/二阶占优

[D3] 是判定条件 E[belief] > E[X]；[E1] 是更强的可证明模型 belief = X + a。
不能把两者混同：均值提高本身并不控制每个阈值处的累计概率。
-/
noncomputable section
open MeasureTheory Set Filter
namespace Overconfidence
variable {Ω : Type*} [MeasurableSpace Ω]

/-- [E1] 位置偏移模型 Xᵉ(ω) = X(ω) + a。a > 0 表示向上高估。 -/
def shift (X : Ω → ℝ) (a : ℝ) : Ω → ℝ := fun ω => X ω + a

/-- [E2] 平移保持可积性。 -/
theorem integrable_shift (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (a : ℝ) : Integrable (shift X a) P :=
  hX.add (integrable_const a)

/-- [E3] E[X+a] = E[X]+a：偏差参数确实就是均值偏差。 -/
theorem mean_shift (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (a : ℝ) :
    mean P (shift X a) = mean P X + a := by
  simp only [mean, shift, integral_add hX (integrable_const a), integral_const,
    probReal_univ, smul_eq_mul, one_mul]

/-- [E4] 在该模型中，overestimation ⇔ a > 0。 -/
theorem overestimation_shift_iff (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (a : ℝ) :
    Overestimation P X (shift X a) ↔ 0 < a := by
  simp only [Overestimation, mean_shift P hX a]
  constructor
  · rintro ⟨_, _, h⟩
    linarith
  · intro h
    exact ⟨hX, integrable_shift P hX a, by linarith⟩

/-- [E5] 平移不改变方差；即使均值提高，也不是“更精确”。 -/
theorem variance_shift (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (a : ℝ) :
    variance P (shift X a) = variance P X := by
  unfold variance
  rw [mean_shift P hX a]
  congr 1
  funext ω
  simp only [shift]
  congr 1
  ring

/-- [E6] F_{X+a}(t) = F_X(t−a)，直接证明分布的平移公式。 -/
theorem cdf_shift (P : Measure Ω) (X : Ω → ℝ) (a t : ℝ) :
    cdf P (shift X a) t = cdf P X (t - a) := by
  unfold cdf
  congr 1
  ext ω
  simp only [mem_preimage, mem_Iic, shift]
  constructor <;> intro h <;> linarith

/-- [E7] a≥0 ⇒ X ≤st X+a；复用共同样本空间的有序耦合。 -/
theorem shift_fsd (P : Measure Ω) (X : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    FSD P X (shift X a) := by
  apply fsd_of_ae_le
  exact Filter.Eventually.of_forall (fun ω => by dsimp [shift]; linarith)

/-- [E8] 更强结论：每个可积递增效用都提高。 -/
theorem shift_utilityLE (P : Measure Ω) (X : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    UtilityLE P Monotone X (shift X a) := by
  apply utilityLE_of_ae_le
  exact Filter.Eventually.of_forall (fun ω => by dsimp [shift]; linarith)

/-- [E9] 因而也有二阶随机占优 X ≤icv X+a。 -/
theorem shift_ssd (P : Measure Ω) (X : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    SSD P X (shift X a) := by
  apply ssd_of_ae_le
  exact Filter.Eventually.of_forall (fun ω => by dsimp [shift]; linarith)

/-- [E10] 随机而非常数的非负偏差 D 也足以推出 FSD，无需独立性。 -/
theorem nonnegative_bias_fsd (P : Measure Ω) (X D : Ω → ℝ)
    (hD : 0 ≤ᵐ[P] D) : FSD P X (fun ω => X ω + D ω) := by
  apply fsd_of_ae_le
  filter_upwards [hD] with ω hω
  exact le_add_of_nonneg_right hω

/-- [E11] 偏差参数的比较静态：a≤b ⇒ X+a ≤st X+b。 -/
theorem shift_fsd_mono (P : Measure Ω) (X : Ω → ℝ) {a b : ℝ} (hab : a ≤ b) :
    FSD P (shift X a) (shift X b) := by
  apply fsd_of_ae_le
  exact Filter.Eventually.of_forall (fun ω => by dsimp [shift]; linarith)

end Overconfidence

end -- close the source file noncomputable section

/-! ## Source module: Overconfidence/Placement.lean -/
/-!
# Overplacement：相对差值与百分位的两个明确模型

`X` 是自己的实际表现，`B` 是参照者的实际表现；两者可以相关。
主观表现分别为 `X + a` 和 `B + b`，因此关键参数是相对偏移 `a - b`。
所有随机序都比较相同量纲的对象：相对差值和相对差值、百分位和百分位。
这里没有把相对表现分布直接与绝对表现 `X` 的分布混为一谈。
-/
noncomputable section
open MeasureTheory Set Filter
open scoped ENNReal
namespace Overconfidence

variable {Ω : Type*}

/-- [L1] 主观相对差值 R̂ = (X + a) − (B + b)。 -/
def perceivedGap (X B : Ω → ℝ) (a b : ℝ) : Ω → ℝ :=
  relative (fun ω => X ω + a) (fun ω => B ω + b)

/-- [L2] 分解恒等式：R̂ = R + (a − b)。这是后续随机序的有序耦合。 -/
theorem perceivedGap_eq (X B : Ω → ℝ) (a b : ℝ) :
    perceivedGap X B a b = fun ω => relative X B ω + (a - b) := by
  funext ω
  simp only [perceivedGap, relative]
  ring

/-- [L3] 当两个主观偏差相同，相对分布完全不变。 -/
theorem perceivedGap_same_shift (X B : Ω → ℝ) (a : ℝ) :
    perceivedGap X B a a = relative X B := by
  rw [perceivedGap_eq]
  simp

variable [MeasurableSpace Ω]

/-- [L4] E[R̂] = E[R] + a − b；有限均值假设明确放在输入中。 -/
theorem mean_perceivedGap (P : Measure Ω) [IsProbabilityMeasure P]
    {X B : Ω → ℝ} (hX : Integrable X P) (hB : Integrable B P) (a b : ℝ) :
    mean P (perceivedGap X B a b) = mean P (relative X B) + (a - b) := by
  rw [perceivedGap_eq]
  simpa only [mean, relative, Pi.sub_apply, integral_const, probReal_univ,
    smul_eq_mul, one_mul] using integral_add (hX.sub hB) (integrable_const (a - b))

/-- [L5] 在加性偏差模型中，overplacement 当且仅当 a > b。
只有 a > 0（高估自己的绝对表现）不足以推出 overplacement。 -/
theorem overplacement_iff (P : Measure Ω) [IsProbabilityMeasure P]
    {X B : Ω → ℝ} (hX : Integrable X P) (hB : Integrable B P) (a b : ℝ) :
    Overplacement P X B (fun ω => X ω + a) (fun ω => B ω + b) ↔ b < a := by
  have hR : Integrable (relative X B) P := hX.sub hB
  have hG : Integrable (perceivedGap X B a b) P := by
    rw [perceivedGap_eq]
    exact hR.add (integrable_const (a - b))
  change (Integrable (relative X B) P ∧ Integrable (perceivedGap X B a b) P ∧
    mean P (relative X B) < mean P (perceivedGap X B a b)) ↔ b < a
  rw [mean_perceivedGap P hX hB a b]
  constructor
  · intro h
    linarith [h.2.2]
  · intro h
    exact ⟨hR, hG, by linarith⟩

/-- [L6] 精确 CDF 公式：F_R̂(t) = F_R(t − (a − b))。
证明使用事件恒等式，不要求 X 和 B 独立。 -/
theorem cdf_perceivedGap (P : Measure Ω) (X B : Ω → ℝ) (a b t : ℝ) :
    cdf P (perceivedGap X B a b) t = cdf P (relative X B) (t - (a - b)) := by
  rw [perceivedGap_eq]
  unfold cdf
  congr 1
  ext ω
  simp only [mem_preimage, mem_Iic]
  constructor <;> intro h <;> linarith

/-- [L7] a ≥ b ⇒ R̂ 一阶随机占优 R。 -/
theorem placement_fsd (P : Measure Ω) (X B : Ω → ℝ) {a b : ℝ} (hab : b ≤ a) :
    FSD P (relative X B) (perceivedGap X B a b) := by
  apply fsd_of_ae_le
  rw [perceivedGap_eq]
  exact Filter.Eventually.of_forall (fun ω => by dsimp; linarith)

/-- [L8] 相同的逐状态单调性同时给出递增凹效用意义的 SSD。 -/
theorem placement_ssd (P : Measure Ω) (X B : Ω → ℝ) {a b : ℝ} (hab : b ≤ a) :
    SSD P (relative X B) (perceivedGap X B a b) := by
  apply ssd_of_ae_le
  rw [perceivedGap_eq]
  exact Filter.Eventually.of_forall (fun ω => by dsimp; linarith)

/-- [L9] a ≤ b 时一阶随机占优方向反转。 -/
theorem placement_fsd_reverse (P : Measure Ω) (X B : Ω → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    FSD P (perceivedGap X B a b) (relative X B) := by
  apply fsd_of_ae_le
  rw [perceivedGap_eq]
  exact Filter.Eventually.of_forall (fun ω => by dsimp; linarith)

/-- [L10] a ≤ b 时二阶随机占优方向也反转。 -/
theorem placement_ssd_reverse (P : Measure Ω) (X B : Ω → ℝ)
    {a b : ℝ} (hab : a ≤ b) :
    SSD P (perceivedGap X B a b) (relative X B) := by
  apply ssd_of_ae_le
  rw [perceivedGap_eq]
  exact Filter.Eventually.of_forall (fun ω => by dsimp; linarith)

/-- [L11] 百分位版本：Rank_H(X) = H(X)，H 是固定参照分布的 CDF。
约定数值越大排名越好；H(X) 计算参照表现不超过 X 的比例（包含并列）。 -/
def percentile (H : ℝ → ℝ) (X : Ω → ℝ) : Ω → ℝ := H ∘ X

/-- [L12] 固定参照下，a ≥ 0 ⇒ H(X+a) 一阶随机占优 H(X)。
H 只需单调；H 的平坦区意味着弱占优不一定严格。 -/
theorem percentile_fsd (P : Measure Ω) (H : ℝ → ℝ) (hH : Monotone H)
    (X : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    FSD P (percentile H X) (percentile H (fun ω => X ω + a)) := by
  apply fsd_of_ae_le
  exact Filter.Eventually.of_forall (fun ω => hH (by linarith))

/-- [L13] 百分位版本同样具有 SSD。 -/
theorem percentile_ssd (P : Measure Ω) (H : ℝ → ℝ) (hH : Monotone H)
    (X : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    SSD P (percentile H X) (percentile H (fun ω => X ω + a)) := by
  apply ssd_of_ae_le
  exact Filter.Eventually.of_forall (fun ω => hH (by linarith))

variable {Λ : Type*} [MeasurableSpace Λ]

/-- [L14] 从实际参照概率空间构造实值 CDF：H_Q,B(t) = Q{B ≤ t}。 -/
def referenceCDF (Q : Measure Λ) (B : Λ → ℝ) (t : ℝ) : ℝ :=
  (cdf Q B t).toReal

/-- [L15] 真正参照 CDF 的单调性由事件包含和测度单调性推出。 -/
theorem referenceCDF_monotone (Q : Measure Λ) [IsProbabilityMeasure Q]
    (B : Λ → ℝ) : Monotone (referenceCDF Q B) := by
  intro s t hst
  apply ENNReal.toReal_mono (measure_ne_top Q _)
  apply measure_mono
  exact fun _ hω => le_trans hω hst

/-- [L16] 百分位确实属于 [0,1]，而不是任意单调分数。 -/
theorem referenceCDF_mem_unitInterval (Q : Measure Λ) [IsProbabilityMeasure Q]
    (B : Λ → ℝ) (t : ℝ) : referenceCDF Q B t ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact ENNReal.toReal_nonneg
  · have h : cdf Q B t ≤ 1 := by
      calc
        cdf Q B t ≤ Q univ := measure_mono (subset_univ _)
        _ = 1 := measure_univ
    simpa [referenceCDF] using ENNReal.toReal_mono (by simp : (1 : ℝ≥0∞) ≠ ∞) h

/-- [L17] 将实际参照分布代入 L12，得到排名分布的一阶随机占优。 -/
theorem percentile_reference_fsd (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure Q] (B : Λ → ℝ) (X : Ω → ℝ) {a : ℝ} (ha : 0 ≤ a) :
    FSD P (percentile (referenceCDF Q B) X)
      (percentile (referenceCDF Q B) (fun ω => X ω + a)) :=
  percentile_fsd P _ (referenceCDF_monotone Q B) X ha

/-- [L18] 同时偏移自己和参照群体：H_(B+b)(X+a) = H_B(X+a−b)。
这说明排名模型的有效偏差也是 a−b；这里的参照群体空间可以不同于 Ω。 -/
theorem referenceCDF_shift (Q : Measure Λ) (B : Λ → ℝ) (a b t : ℝ) :
    referenceCDF Q (fun ω => B ω + b) (t + a) =
      referenceCDF Q B (t + (a - b)) := by
  unfold referenceCDF cdf
  congr 2
  ext ω
  simp only [mem_preimage, mem_Iic]
  constructor <;> intro h <;> linarith

/-- [L19] a ≥ b ⇒ 主观百分位 H_(B+b)(X+a) 一阶随机占优客观百分位 H_B(X)。 -/
theorem percentile_placement_fsd (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure Q] (B : Λ → ℝ) (X : Ω → ℝ)
    {a b : ℝ} (hab : b ≤ a) :
    FSD P (percentile (referenceCDF Q B) X)
      (percentile (referenceCDF Q (fun ω => B ω + b)) (fun ω => X ω + a)) := by
  apply fsd_of_ae_le
  apply Filter.Eventually.of_forall
  intro ω
  change referenceCDF Q B (X ω) ≤ referenceCDF Q (fun ω => B ω + b) (X ω + a)
  rw [referenceCDF_shift]
  exact referenceCDF_monotone Q B (by linarith)

/-- [L20] 相同排名耦合也给出递增凹效用意义的二阶随机占优。 -/
theorem percentile_placement_ssd (P : Measure Ω) (Q : Measure Λ)
    [IsProbabilityMeasure Q] (B : Λ → ℝ) (X : Ω → ℝ)
    {a b : ℝ} (hab : b ≤ a) :
    SSD P (percentile (referenceCDF Q B) X)
      (percentile (referenceCDF Q (fun ω => B ω + b)) (fun ω => X ω + a)) := by
  apply ssd_of_ae_le
  apply Filter.Eventually.of_forall
  intro ω
  change referenceCDF Q B (X ω) ≤ referenceCDF Q (fun ω => B ω + b) (X ω + a)
  rw [referenceCDF_shift]
  exact referenceCDF_monotone Q B (by linarith)

/-- [L21] 当参照变量可测时，实值 CDF 就是参照推前概率分布的区间质量。 -/
theorem referenceCDF_eq_law (Q : ProbabilityMeasure Λ) (B : Λ → ℝ)
    (hB : AEMeasurable B (Q : Measure Λ)) (t : ℝ) :
    referenceCDF (Q : Measure Λ) B t = ((law Q B hB : Measure ℝ) (Iic t)).toReal := by
  rw [law_cdf]
  rfl

/-- [L22] 实际百分位是可测随机变量，因此也可用 `law` 构造其概率分布。 -/
theorem percentile_reference_measurable (Q : Measure Λ) [IsProbabilityMeasure Q]
    (B : Λ → ℝ) {X : Ω → ℝ} (hX : Measurable X) :
    Measurable (percentile (referenceCDF Q B) X) :=
  (referenceCDF_monotone Q B).measurable.comp hX

end Overconfidence

end -- close the source file noncomputable section

/-! ## Source module: Overconfidence/Precision.lean -/
/-!
# Overprecision：围绕均值的收缩与凸序

本文件选择保均值收缩模型 `X_c = μ + c (X - μ)`，其中 `0 ≤ c ≤ 1`。
这是一种具体、可验证的过度精确表现：中心判断正确，但主观分布过窄。
结论使用真实概率测度上的积分；不把 Jensen 不等式或随机占优当成假设。
-/
noncomputable section
open MeasureTheory Set Filter
namespace Overconfidence

variable {Ω : Type*} [MeasurableSpace Ω]

/-- [P1] X_c = μ + c(X−μ)，μ = E[X]；c 越小，主观分布越集中。 -/
def contraction (P : Measure Ω) (X : Ω → ℝ) (c : ℝ) : Ω → ℝ :=
  fun ω => mean P X + c * (X ω - mean P X)

/-- [P1a] c=0 时，所有主观概率质量集中在 μ。 -/
theorem contraction_zero (P : Measure Ω) (X : Ω → ℝ) :
    contraction P X 0 = fun _ => mean P X := by
  funext ω
  simp [contraction]

/-- [P1b] c=1 时，主观随机变量等于原随机变量。 -/
theorem contraction_one (P : Measure Ω) (X : Ω → ℝ) : contraction P X 1 = X := by
  funext ω
  simp [contraction]

/-- [P1c] c>0 时的完整分布公式：F_Xc(t)=F_X(μ+(t−μ)/c)。
它将收缩后的每个概率阈值还原为原分布的阈值。 -/
theorem cdf_contraction (P : Measure Ω) (X : Ω → ℝ) {c : ℝ} (hc : 0 < c) (t : ℝ) :
    cdf P (contraction P X c) t = cdf P X (mean P X + (t - mean P X) / c) := by
  unfold cdf
  congr 1
  ext ω
  simp only [mem_preimage, mem_Iic, contraction]
  constructor
  · intro h
    have hz : X ω - mean P X ≤ (t - mean P X) / c :=
      (le_div_iff₀ hc).2 (by nlinarith)
    linarith
  · intro h
    have hz : (X ω - mean P X) * c ≤ t - mean P X :=
      (le_div_iff₀ hc).1 (by linarith)
    nlinarith

/-- [P1d] 完全收缩的 CDF：μ 以下为 0，μ 及以上为 1。 -/
theorem cdf_contraction_zero (P : Measure Ω) [IsProbabilityMeasure P]
    (X : Ω → ℝ) (t : ℝ) :
    cdf P (contraction P X 0) t = if mean P X ≤ t then 1 else 0 := by
  rw [contraction_zero]
  by_cases h : mean P X ≤ t <;> simp [cdf, Set.preimage, h]

/-- [P1e] 若 0<c≤1，则在均值左侧 F_Xc(t)≤F_X(t)：收缩减少左尾风险。 -/
theorem cdf_contraction_below_mean (P : Measure Ω) (X : Ω → ℝ)
    {c t : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (ht : t ≤ mean P X) :
    cdf P (contraction P X c) t ≤ cdf P X t := by
  rw [cdf_contraction P X hc0 t]
  apply measure_mono
  intro ω hω
  have hquot : (t - mean P X) / c ≤ t - mean P X :=
    (div_le_iff₀ hc0).2 (by nlinarith)
  change X ω ≤ mean P X + (t - mean P X) / c at hω
  change X ω ≤ t
  linarith

/-- [P1f] 若 0<c≤1，则在均值右侧 F_X(t)≤F_Xc(t)：收缩同时减少右尾。
两侧方向相反，因此一般不能从 overprecision 推出一阶随机占优。 -/
theorem cdf_contraction_above_mean (P : Measure Ω) (X : Ω → ℝ)
    {c t : ℝ} (hc0 : 0 < c) (hc1 : c ≤ 1) (ht : mean P X ≤ t) :
    cdf P X t ≤ cdf P (contraction P X c) t := by
  rw [cdf_contraction P X hc0 t]
  apply measure_mono
  intro ω hω
  have hquot : t - mean P X ≤ (t - mean P X) / c :=
    (le_div_iff₀ hc0).2 (by nlinarith)
  change X ω ≤ t at hω
  change X ω ≤ mean P X + (t - mean P X) / c
  linarith

/-- [P2] 收缩后仍可积，因此主观均值是合法的期望。 -/
theorem integrable_contraction (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (c : ℝ) :
    Integrable (contraction P X c) P :=
  (integrable_const _).add ((hX.sub (integrable_const _)).const_mul c)

/-- [P3] E[X_c] = μ + c(E[X]−μ) = μ：单独改变精确度不改变平均判断。 -/
theorem mean_contraction (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (c : ℝ) :
    mean P (contraction P X c) = mean P X := by
  unfold mean contraction
  rw [integral_add (f := fun _ : Ω => mean P X)
    (g := fun ω => c * (X ω - mean P X))
    (integrable_const _) ((hX.sub (integrable_const _)).const_mul c)]
  rw [integral_const_mul,
    integral_sub (f := X) (g := fun _ : Ω => mean P X) hX (integrable_const _)]
  simp [mean]

/-- [P4] 中心化平方满足 (X_c−E[X_c])² = c²(X−μ)²。 -/
theorem contraction_centered_sq (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (c : ℝ) (ω : Ω) :
    (contraction P X c ω - mean P (contraction P X c)) ^ 2 =
      c ^ 2 * (X ω - mean P X) ^ 2 := by
  rw [mean_contraction P hX c]
  unfold contraction
  ring

/-- [P5] 二阶矩条件随收缩保留；它保证方差比较有概率意义。 -/
theorem integrable_contraction_centered_sq (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P)
    (hV : Integrable (fun ω => (X ω - mean P X) ^ 2) P) (c : ℝ) :
    Integrable (fun ω => (contraction P X c ω - mean P (contraction P X c)) ^ 2) P := by
  simpa only [contraction_centered_sq P hX c] using hV.const_mul (c ^ 2)

/-- [P6] Var(X_c) = c² Var(X)：这是精确度参数的精确数量含义。 -/
theorem variance_contraction (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) (c : ℝ) :
    variance P (contraction P X c) = c ^ 2 * variance P X := by
  simp only [variance, contraction_centered_sq P hX c, integral_const_mul]

/-- [P7] 若 Var(X)>0 且 0≤c<1，则主观分布满足严格的 overprecision 定义。
排除零方差是必要的：常数随机变量无法再严格收缩。 -/
theorem overprecision_contraction (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P)
    (hV : Integrable (fun ω => (X ω - mean P X) ^ 2) P)
    (hVar : 0 < variance P X) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) :
    Overprecision P X (contraction P X c) := by
  refine ⟨hX, integrable_contraction P hX c,
    hV, integrable_contraction_centered_sq P hX hV c,
    mean_contraction P hX c, ?_⟩
  rw [variance_contraction P hX c]
  have hc : c ^ 2 < 1 := by nlinarith
  nlinarith

/-- [P8] X_c ≤cx X：Jensen + 逐点凸组合不等式证明保均值收缩减少所有凸损失。
φ(X_c) ≤ (1−c)φ(μ)+cφ(X)，且 φ(μ)≤E[φ(X)]。
本结论强于单独比较方差；不要求二阶矩存在。 -/
theorem contraction_convexLE (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ConvexLE P (contraction P X c) X := by
  intro u hu huC huX
  have hJ : u (mean P X) ≤ ∫ ω, u (X ω) ∂P := by
    exact hu.map_integral_le (hu.continuousOn isOpen_univ) isClosed_univ
      (Filter.Eventually.of_forall (fun _ => mem_univ _)) hX huX
  have hp : ∀ ω, u (contraction P X c ω) ≤
      (1 - c) * u (mean P X) + c * u (X ω) := by
    intro ω
    have h := hu.2 (mem_univ (mean P X)) (mem_univ (X ω))
      (sub_nonneg.mpr hc1) hc0 (by ring : 1 - c + c = 1)
    simp only [smul_eq_mul] at h
    calc
      u (contraction P X c ω) = u ((1 - c) * mean P X + c * X ω) := by
        congr 1
        unfold contraction
        ring
      _ ≤ (1 - c) * u (mean P X) + c * u (X ω) := h
  have hi := integral_mono huC
    ((integrable_const ((1 - c) * u (mean P X))).add (huX.const_mul c)) hp
  change (∫ ω, u (contraction P X c ω) ∂P) ≤
    ∫ ω, (1 - c) * u (mean P X) + c * u (X ω) ∂P at hi
  rw [integral_add (f := fun _ : Ω => (1 - c) * u (mean P X))
    (g := fun ω => c * u (X ω)) (integrable_const _) (huX.const_mul c),
    integral_const_mul] at hi
  simp only [integral_const_mul, integral_const, probReal_univ, smul_eq_mul, one_mul] at hi
  have hw := mul_le_mul_of_nonneg_left hJ (sub_nonneg.mpr hc1)
  linarith

/-- [P9] 一般桥梁：Y ≤cx X ⇒ X ≤icv Y。
令 φ = −u：凹效用 u 对较集中的 Y 给出较高期望效用。 -/
theorem ssd_of_reverse_convexLE (P : Measure Ω) {X Y : Ω → ℝ}
    (h : ConvexLE P Y X) : SSD P X Y := by
  intro u hu huX huY
  have hn := h (fun x => -u x) hu.2.neg huY.neg huX.neg
  simp only [integral_neg] at hn
  linarith

/-- [P10] X ≤icv X_c：在相同均值下，收缩后的主观分布二阶随机占优原分布。
方向必须区分：凸序把更分散的 X 放在右侧，凹效用序把更集中的 X_c 放在右侧。 -/
theorem ssd_contraction (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) : SSD P X (contraction P X c) :=
  ssd_of_reverse_convexLE P (contraction_convexLE P hX hc0 hc1)

end Overconfidence

end -- close the source file noncomputable section

/-! ## Source module: Overconfidence/Risk.lean -/
/-!
# 下偏矩：二阶与更高阶的分布比较

L_k(X;t) = E[(t−X)_+^k]，k=1 为阈值下的期望缺口，k=2 为平方短缺。
若在共同有限下界 ℓ 以上，L_k/k! 是 CDF 的 k 次积分（k≥1）。
此文件直接证明所有自然数 k 的下偏矩不等式。
不把未在此证明的 CDF 积分表示/高阶效用等价定理当作已完成的 Lean 定理。
-/
noncomputable section
open MeasureTheory Set Filter
namespace Overconfidence
variable {Ω : Type*} [MeasurableSpace Ω]

/-- [H1] (t−x)_+^k 是阈值 t 下的 k 次短缺损失。 -/
def downside (k : ℕ) (t x : ℝ) : ℝ := max (t - x) 0 ^ k

/-- [H2] 下偏矩 L_k(X;t)。实际调用定理时须验证相应损失的可积性。 -/
def lowerPartialMoment (P : Measure Ω) (X : Ω → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  ∫ ω, downside k t (X ω) ∂P

/-- [H3] 所有自然数次的短缺损失都是凸函数（包括 k=0 的常数情形）。 -/
theorem convex_downside (k : ℕ) (t : ℝ) :
    ConvexOn ℝ univ (downside k t) := by
  have ha : ConvexOn ℝ univ (fun x : ℝ => t - x) := by
    refine ⟨convex_univ, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    have ht : (a + b) * t = t := by rw [hab]; ring
    nlinarith [ht]
  have hm : ConvexOn ℝ univ (fun x : ℝ => max (t - x) 0) :=
    ha.sup (convexOn_const 0 convex_univ)
  exact hm.pow (fun _ _ => le_max_right _ _) k

/-- [H4] x 越大，短缺损失越小。 -/
theorem antitone_downside (k : ℕ) (t : ℝ) : Antitone (downside k t) := by
  intro x y hxy
  apply pow_le_pow_left₀ (le_max_right _ _)
  exact max_le_max (sub_le_sub_left hxy t) le_rfl

/-- [H5] 有序耦合 ⇒ 每个可积下偏矩均减少；不需要独立性。 -/
theorem lowerPartialMoment_le_of_ae_le (P : Measure Ω) {X Y : Ω → ℝ}
    (hXY : X ≤ᵐ[P] Y) (k : ℕ) (t : ℝ)
    (hX : Integrable (fun ω => downside k t (X ω)) P)
    (hY : Integrable (fun ω => downside k t (Y ω)) P) :
    lowerPartialMoment P Y k t ≤ lowerPartialMoment P X k t := by
  apply integral_mono_ae hY hX
  filter_upwards [hXY] with ω hω
  exact antitone_downside k t hω

/-- [H6] 位置型 overestimation：L_k(X+a;t) ≤ L_k(X;t)，a≥0。 -/
theorem shift_lowerPartialMoment (P : Measure Ω) (X : Ω → ℝ)
    {a : ℝ} (ha : 0 ≤ a) (k : ℕ) (t : ℝ)
    (hX : Integrable (fun ω => downside k t (X ω)) P)
    (hY : Integrable (fun ω => downside k t (shift X a ω)) P) :
    lowerPartialMoment P (shift X a) k t ≤ lowerPartialMoment P X k t := by
  apply lowerPartialMoment_le_of_ae_le P _ k t hX hY
  exact Filter.Eventually.of_forall (fun ω => by dsimp [shift]; linarith)

/-- [H6b] 相对表现的下偏矩：a≥b 时 L_k(R̂;t)≤L_k(R;t)。 -/
theorem placement_lowerPartialMoment (P : Measure Ω) (X B : Ω → ℝ)
    {a b : ℝ} (hab : b ≤ a) (k : ℕ) (t : ℝ)
    (hR : Integrable (fun ω => downside k t (relative X B ω)) P)
    (hG : Integrable (fun ω => downside k t (perceivedGap X B a b ω)) P) :
    lowerPartialMoment P (perceivedGap X B a b) k t ≤
      lowerPartialMoment P (relative X B) k t := by
  apply lowerPartialMoment_le_of_ae_le P _ k t hR hG
  rw [perceivedGap_eq]
  exact Filter.Eventually.of_forall (fun ω => by dsimp; linarith)

/-- [H7] 保均值收缩：L_k(X_c;t) ≤ L_k(X;t)，0≤c≤1。
这里使用已证明的凸序而非方差比较，因此同时控制所有阈值和所有可积阶数。 -/
theorem contraction_lowerPartialMoment (P : Measure Ω) [IsProbabilityMeasure P]
    {X : Ω → ℝ} (hX : Integrable X P) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (k : ℕ) (t : ℝ)
    (hCX : Integrable (fun ω => downside k t (contraction P X c ω)) P)
    (hXX : Integrable (fun ω => downside k t (X ω)) P) :
    lowerPartialMoment P (contraction P X c) k t ≤ lowerPartialMoment P X k t := by
  exact contraction_convexLE P hX hc0 hc1 (downside k t) (convex_downside k t) hCX hXX

end Overconfidence

end -- close the source file noncomputable section

/-! ## Source module: Overconfidence/Counterexamples.lean -/
/-!
# 反例：心理学定义本身不能推出完整的随机占优

本文件使用真实的两点概率测度 P = (1/4)δ₀ + (3/4)δ₁。
所有积分都直接化为带概率权重的有限和，不引入抽象期望算子。
-/
noncomputable section
open MeasureTheory Set
open scoped ENNReal
namespace Overconfidence.Counterexamples

/-- [C0] 两点实验的概率分别为 1/4、3/4。 -/
def P : Measure ℝ := (1 / 4 : ℝ≥0∞) • Measure.dirac 0 +
  (3 / 4 : ℝ≥0∞) • Measure.dirac 1

private theorem weights_sum : (1 / 4 : ℝ≥0∞) + 3 / 4 = 1 := by
  calc
    (1 / 4 : ℝ≥0∞) + 3 / 4 = (1 + 3) / 4 := ENNReal.div_add_div_same
    _ = 4 / 4 := by norm_num
    _ = 1 := ENNReal.div_self (by norm_num) (by norm_num)

private theorem weights_sum_normalized : (4 : ℝ≥0∞)⁻¹ + 3 / 4 = 1 := by
  simpa only [one_div] using weights_sum

instance : IsProbabilityMeasure P := by
  constructor
  simpa [P, Measure.add_apply, Measure.smul_apply] using weights_sum

/-- 两点测度下任意实值函数可积。 -/
theorem integrable_P (f : ℝ → ℝ) : Integrable f P := by
  apply Integrable.add_measure
  · exact (integrable_dirac (by simp)).smul_measure
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure
      (ENNReal.div_ne_top (by norm_num) (by norm_num))

/-- [C1] E_P[f] = f(0)/4 + 3 f(1)/4。 -/
theorem integral_P (f : ℝ → ℝ) :
    (∫ ω, f ω ∂P) = (1 / 4 : ℝ) * f 0 + (3 / 4 : ℝ) * f 1 := by
  rw [P, integral_add_measure]
  · simp only [integral_smul_measure, integral_dirac, smul_eq_mul]
    norm_num
  · exact (integrable_dirac (by simp)).smul_measure
      (ENNReal.div_ne_top (by norm_num) (by norm_num))
  · exact (integrable_dirac (by simp)).smul_measure
      (ENNReal.div_ne_top (by norm_num) (by norm_num))

/-- [C2] CDF 是两个指示函数的带权和。 -/
theorem cdf_P (X : ℝ → ℝ) (t : ℝ) :
    cdf P X t = (1 / 4 : ℝ≥0∞) * (if X 0 ≤ t then 1 else 0) +
      (3 / 4 : ℝ≥0∞) * (if X 1 ≤ t then 1 else 0) := by
  by_cases h0 : X 0 ≤ t <;> by_cases h1 : X 1 ≤ t <;>
    simp [cdf, P, Measure.add_apply, Measure.smul_apply, Measure.dirac_apply,
      Set.indicator, h0, h1]

/-- [C3] u_t(x)=min(x,t) 是递增凹效用，可检测分布的下尾风险。 -/
theorem capped_utility (t : ℝ) :
    Monotone (fun x : ℝ => min x t) ∧
      ConcaveOn ℝ univ (fun x : ℝ => min x t) := by
  constructor
  · intro a b hab
    exact min_le_min_right t hab
  · exact (concaveOn_id convex_univ).inf (concaveOn_const t convex_univ)

/-- 基准表现恒为 0。 -/
def zero : ℝ → ℝ := fun _ => 0

/-- [C4] 主观表现取 -1（概率 1/4）、1（概率 3/4），均值 1/2。 -/
def optimistic : ℝ → ℝ := fun ω => 2 * ω - 1

theorem optimistic_mean : mean P optimistic = 1 / 2 := by
  rw [mean, integral_P]
  norm_num [optimistic]

theorem zero_mean : mean P zero = 0 := by
  rw [mean, integral_P]
  norm_num [zero]

/-- [C5] E[主观表现]=1/2>0，满足 overestimation 的均值定义。 -/
theorem optimistic_overestimation : Overestimation P zero optimistic := by
  refine ⟨integrable_P _, integrable_P _, ?_⟩
  rw [zero_mean, optimistic_mean]
  norm_num

/-- [C6] 在 t=-1/2 处，F_主观=1/4>F_基准=0，所以主观分布不 FSD 占优。 -/
theorem optimistic_not_fsd : ¬ FSD P zero optimistic := by
  intro h
  have h' := h (-1 / 2)
  norm_num [cdf_P, optimistic, zero, weights_sum_normalized] at h'

/-- [C7] 在 t=1/2 处，F_基准=1>F_主观=1/4，反方向也不 FSD 占优。 -/
theorem optimistic_not_fsd_reverse : ¬ FSD P optimistic zero := by
  intro h
  have h' := h (1 / 2)
  norm_num [cdf_P, optimistic, zero, weights_sum_normalized] at h'

/-- [C8] u(x)=min(x,0)：E[u(基准)]=0>−1/4=E[u(主观)]，故均值高估不推出 SSD。 -/
theorem optimistic_not_ssd : ¬ SSD P zero optimistic := by
  intro h
  have h' := h (fun x => min x 0) (capped_utility 0) (integrable_P _) (integrable_P _)
  rw [integral_P, integral_P] at h'
  norm_num [optimistic, zero] at h'

/-- [C9] u(x)=x：均值 1/2>0，反方向也不满足 SSD。 -/
theorem optimistic_not_ssd_reverse : ¬ SSD P optimistic zero := by
  intro h
  have h' := h id ⟨monotone_id, concaveOn_id convex_univ⟩
    (integrable_P _) (integrable_P _)
  rw [integral_P, integral_P] at h'
  norm_num [optimistic, zero] at h'

/-- [C10] 原始表现取 -3（概率 1/4）、1（概率 3/4）；均值 0、方差 3。 -/
def dispersed : ℝ → ℝ := fun ω => 4 * ω - 3

theorem dispersed_mean : mean P dispersed = 0 := by
  rw [mean, integral_P]
  norm_num [dispersed]

theorem dispersed_variance : variance P dispersed = 3 := by
  rw [variance, dispersed_mean, integral_P]
  norm_num [dispersed]

/-- 收缩至均值的方差为 0，确实满足这里的 overprecision 定义。 -/
theorem contraction_overprecision : Overprecision P dispersed zero := by
  refine ⟨integrable_P _, integrable_P _, integrable_P _, integrable_P _, ?_, ?_⟩
  · rw [zero_mean, dispersed_mean]
  · rw [dispersed_variance, variance, zero_mean, integral_P]
    norm_num [zero]

/-- [C11] 收缩至均值时，CDF 在 0 两侧交叉；无 FSD（基准→收缩）。 -/
theorem contraction_not_fsd : ¬ FSD P dispersed zero := by
  intro h
  have h' := h 0
  norm_num [cdf_P, dispersed, zero, weights_sum_normalized] at h'

/-- [C12] 收缩至均值也无反方向 FSD。 -/
theorem contraction_not_fsd_reverse : ¬ FSD P zero dispersed := by
  intro h
  have h' := h (-1)
  norm_num [cdf_P, dispersed, zero, weights_sum_normalized] at h'

/-- [C13] 另一个信念分布取 2（概率 1/4）、-2/3（概率 3/4）。
其均值为 0、方差为 4/3，小于原始方差 3，但不是均值保持收缩。 -/
def lowerVariance : ℝ → ℝ := fun ω => 2 - (8 / 3) * ω

theorem lowerVariance_mean : mean P lowerVariance = 0 := by
  rw [mean, integral_P]
  norm_num [lowerVariance]

theorem lowerVariance_variance : variance P lowerVariance = 4 / 3 := by
  rw [variance, lowerVariance_mean, integral_P]
  norm_num [lowerVariance]

/-- [C14] 方差定义的 overprecision 确实成立：均值相同且 4/3<3。 -/
theorem lowerVariance_overprecision : Overprecision P dispersed lowerVariance := by
  refine ⟨integrable_P _, integrable_P _, integrable_P _, integrable_P _, ?_, ?_⟩
  · rw [lowerVariance_mean, dispersed_mean]
  · rw [lowerVariance_variance, dispersed_variance]
    norm_num

/-- [C15] u(x)=min(x,1)：E[u(原始)]=0>−1/4=E[u(信念)]。
所以同均值、方差更小，仍不足以保证信念 SSD 占优原始分布。 -/
theorem lowerVariance_not_ssd : ¬ SSD P dispersed lowerVariance := by
  intro h
  have h' := h (fun x => min x 1) (capped_utility 1) (integrable_P _) (integrable_P _)
  rw [integral_P, integral_P] at h'
  norm_num [dispersed, lowerVariance] at h'

/-- [C16] u(x)=min(x,-1)：E[u(信念)]=−1>−3/2=E[u(原始)]，反向 SSD 也失败。 -/
theorem lowerVariance_not_ssd_reverse : ¬ SSD P lowerVariance dispersed := by
  intro h
  have h' := h (fun x => min x (-1)) (capped_utility (-1))
    (integrable_P _) (integrable_P _)
  rw [integral_P, integral_P] at h'
  norm_num [dispersed, lowerVariance] at h'

end Overconfidence.Counterexamples

end -- close the source file noncomputable section
