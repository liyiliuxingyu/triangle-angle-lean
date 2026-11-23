import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.SplitIfs

/-!
# 三角形最小角、最大角、任意一个角与类型：Lean 4 形式化

实测版本：Lean 4.19.0；mathlib v4.19.0。
mathlib 提交：c44e0c8ee63ca166450922a373c7409c5d26b00b。
检查结果：57 个定理，编译退出码 0，0 错误、0 警告。
公理依赖审查未发现 sorryAx；使用 Lean/mathlib 标准基础公理，不引入自设公理。
在对应的 mathlib 项目目录运行：lake env lean 三角形角度逻辑.lean

所有角度均以“度”为单位，类型为实数 ℝ，不限制为整数。
用 0 < a ≤ b ≤ c、a+b+c=180 表示按大小排列的非退化三角形内角。
因此 a 是最小角，c 是最大角；这里形式化的是角度模型，不涉及坐标作图。

逻辑对应：P → Q 为推出；P ↔ Q 为等价；P ∧ Q 为且；P ∨ Q 为或。
“P 不能保证 Q”用 ¬ (∀ t, P t → Q t) 表达，由具体反例证明。
它不同于 ∀ t, P t → ¬ Q t，后者要求每个满足 P 的对象都不满足 Q。

Lean 检查给定证明是否成立；证明策略失败本身不表示命题为假。
下文将真命题写成定理，将错误的全称反推写成其否定的定理。
-/

namespace TriangleAngleLogic

-- 三个角按从小到大的顺序排列。
structure Triangle where
  a : ℝ
  b : ℝ
  c : ℝ
  a_pos : 0 < a
  ab : a ≤ b
  bc : b ≤ c
  angle_sum : a + b + c = 180

-- 使用原始定义，随后证明它们与最大角条件等价。
def Acute (t : Triangle) : Prop :=
  t.a < 90 ∧ t.b < 90 ∧ t.c < 90

def Right (t : Triangle) : Prop :=
  t.a = 90 ∨ t.b = 90 ∨ t.c = 90

def Obtuse (t : Triangle) : Prop :=
  90 < t.a ∨ 90 < t.b ∨ 90 < t.c

/-! ## 1. 所有三角形的基本范围 -/

-- 最小角总在 (0,60] 中。
theorem min_range (t : Triangle) : 0 < t.a ∧ t.a ≤ 60 := by
  constructor
  · exact t.a_pos
  · linarith [t.ab, t.bc, t.angle_sum]

-- 最大角总在 [60,180) 中。
theorem max_range (t : Triangle) : 60 ≤ t.c ∧ t.c < 180 := by
  constructor
  · linarith [t.ab, t.bc, t.angle_sum]
  · linarith [t.a_pos, t.ab, t.angle_sum]

/-! ## 2. 最大角能完全确定类型 -/

-- 三个角都小于 90，当且仅当最大角小于 90。
theorem acute_iff_max (t : Triangle) : Acute t ↔ t.c < 90 := by
  constructor
  · intro h
    exact h.2.2
  · intro hc
    refine ⟨?_, ?_, hc⟩
    · linarith [t.ab, t.bc]
    · linarith [t.bc]

-- 如存在直角，它只能是最大角。
theorem right_iff_max (t : Triangle) : Right t ↔ t.c = 90 := by
  constructor
  · intro h
    rcases h with ha | hb | hc
    · linarith [(min_range t).2]
    · linarith [t.a_pos, t.bc, t.angle_sum]
    · exact hc
  · intro hc
    exact Or.inr (Or.inr hc)

-- 如存在钝角，最大角必为钝角。
theorem obtuse_iff_max (t : Triangle) : Obtuse t ↔ 90 < t.c := by
  constructor
  · intro h
    rcases h with ha | hb | hc
    · linarith [t.ab, t.bc]
    · linarith [t.bc]
    · exact hc
  · intro hc
    exact Or.inr (Or.inr hc)

-- 锐角三角形 ↔ 60 ≤ 最大角 < 90。
theorem acute_iff_max_range (t : Triangle) :
    Acute t ↔ 60 ≤ t.c ∧ t.c < 90 := by
  constructor
  · intro h
    exact ⟨(max_range t).1, (acute_iff_max t).mp h⟩
  · intro h
    exact (acute_iff_max t).mpr h.2

-- 钝角三角形 ↔ 90 < 最大角 < 180。
theorem obtuse_iff_max_range (t : Triangle) :
    Obtuse t ↔ 90 < t.c ∧ t.c < 180 := by
  constructor
  · intro h
    exact ⟨(obtuse_iff_max t).mp h, (max_range t).2⟩
  · intro h
    exact (obtuse_iff_max t).mpr h.1

/-! ## 3. 已知类型，推出最小角的必要范围 -/

-- 锐角三角形 → 0 < 最小角 ≤ 60；该范围事实上对所有三角形成立。
theorem acute_min_range (t : Triangle) :
    Acute t → 0 < t.a ∧ t.a ≤ 60 := by
  intro _
  exact min_range t

-- 直角三角形 → 0 < 最小角 ≤ 45。
theorem right_min_range (t : Triangle) :
    Right t → 0 < t.a ∧ t.a ≤ 45 := by
  intro h
  have hc := (right_iff_max t).mp h
  refine ⟨t.a_pos, ?_⟩
  linarith [t.ab, t.angle_sum]

-- 钝角三角形 → 0 < 最小角 < 45。
theorem obtuse_min_range (t : Triangle) :
    Obtuse t → 0 < t.a ∧ t.a < 45 := by
  intro h
  have hc := (obtuse_iff_max t).mp h
  refine ⟨t.a_pos, ?_⟩
  linarith [t.ab, t.angle_sum]

/-! ## 4. 已知最小角，能保证什么 -/

-- 最小角 > 45 → 锐角三角形。
-- 最小角 ≤ 60 已由结构条件和 min_range 自动保证。
theorem min_gt_45_acute (t : Triangle) : 45 < t.a → Acute t := by
  intro ha
  apply (acute_iff_max t).mpr
  linarith [t.ab, t.angle_sum]

-- 最小角 = 45 → 锐角三角形或直角三角形。
theorem min_eq_45_acute_or_right (t : Triangle) :
    t.a = 45 → Acute t ∨ Right t := by
  intro ha
  have hc : t.c ≤ 90 := by
    linarith [t.ab, t.angle_sum]
  rcases lt_or_eq_of_le hc with hlt | heq
  · exact Or.inl ((acute_iff_max t).mpr hlt)
  · exact Or.inr ((right_iff_max t).mpr heq)

-- 最小角 ≥ 45 → 不可能是钝角三角形。
theorem min_ge_45_not_obtuse (t : Triangle) :
    45 ≤ t.a → ¬ Obtuse t := by
  intro ha ho
  have hsmall := (obtuse_min_range t ho).2
  linarith

/-! ## 5. 具体见证：相同最小角可以对应不同类型 -/

def acute30 : Triangle where
  a := 30
  b := 75
  c := 75
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

def right30 : Triangle where
  a := 30
  b := 60
  c := 90
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

def obtuse30 : Triangle where
  a := 30
  b := 40
  c := 110
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

def acute45 : Triangle where
  a := 45
  b := 60
  c := 75
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

def right45 : Triangle where
  a := 45
  b := 45
  c := 90
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

-- Lean 同时检查三个 30 度见证的类型和最小角。
theorem three_types_at_30 :
    (Acute acute30 ∧ acute30.a = 30) ∧
    (Right right30 ∧ right30.a = 30) ∧
    (Obtuse obtuse30 ∧ obtuse30.a = 30) := by
  norm_num [Acute, Right, Obtuse, acute30, right30, obtuse30]

-- 最小角恰好 45 度时，两种类型确实都存在。
theorem two_types_at_45 :
    (Acute acute45 ∧ acute45.a = 45) ∧
    (Right right45 ∧ right45.a = 45) := by
  norm_num [Acute, Right, acute45, right45]

/-! ## 6. 错误反推：证明“该全称命题不成立” -/

-- 错：锐角三角形 → 最小角 > 45。
-- 反例：(30,75,75)。
theorem not_every_acute_has_min_gt_45 :
    ¬ (∀ t : Triangle, Acute t → 45 < t.a) := by
  intro h
  have hbad := h acute30 (by norm_num [Acute, acute30])
  norm_num [acute30] at hbad

-- 错：0 < 最小角 ≤ 60 → 锐角三角形。
-- 反例：(30,60,90)。
theorem min_le_60_does_not_force_acute :
    ¬ (∀ t : Triangle, 0 < t.a ∧ t.a ≤ 60 → Acute t) := by
  intro h
  have hbad := h right30 (by norm_num [right30])
  norm_num [Acute, right30] at hbad

-- 错：0 < 最小角 ≤ 45 → 直角三角形。
-- 反例：(30,75,75)。
theorem min_le_45_does_not_force_right :
    ¬ (∀ t : Triangle, 0 < t.a ∧ t.a ≤ 45 → Right t) := by
  intro h
  have hbad := h acute30 (by norm_num [acute30])
  norm_num [Right, acute30] at hbad

-- 错：0 < 最小角 < 45 → 钝角三角形。
-- 反例：(30,75,75)。
theorem min_lt_45_does_not_force_obtuse :
    ¬ (∀ t : Triangle, 0 < t.a ∧ t.a < 45 → Obtuse t) := by
  intro h
  have hbad := h acute30 (by norm_num [acute30])
  norm_num [Obtuse, acute30] at hbad

-- 错：0 < 最小角 < 45 → 锐角三角形。
-- 反例：(30,40,110)。
theorem min_lt_45_does_not_force_acute :
    ¬ (∀ t : Triangle, 0 < t.a ∧ t.a < 45 → Acute t) := by
  intro h
  have hbad := h obtuse30 (by norm_num [obtuse30])
  norm_num [Acute, obtuse30] at hbad

-- 错：最小角 = 45 → 锐角三角形。
-- 反例：(45,45,90)。
theorem min_eq_45_does_not_force_acute :
    ¬ (∀ t : Triangle, t.a = 45 → Acute t) := by
  intro h
  have hbad := h right45 (by norm_num [right45])
  norm_num [Acute, right45] at hbad

-- 错：最小角 = 45 → 直角三角形。
-- 反例：(45,60,75)。
theorem min_eq_45_does_not_force_right :
    ¬ (∀ t : Triangle, t.a = 45 → Right t) := by
  intro h
  have hbad := h acute45 (by norm_num [acute45])
  norm_num [Right, acute45] at hbad

end TriangleAngleLogic

/-! ## 7. 精确区分“存在某类三角形”与“所有对应三角形都属于该类” -/

namespace TriangleAngleLogic

-- 对任意 0 < m ≤ 60，构造最小角为 m 的锐角三角形。
-- noncomputable 用于实数除法的非可执行定义，不省略任何证明。
noncomputable def acuteWithMin (m : ℝ) (hm0 : 0 < m) (hm60 : m ≤ 60) : Triangle where
  a := m
  b := 90 - m / 2
  c := 90 - m / 2
  a_pos := hm0
  ab := by linarith
  bc := le_rfl
  angle_sum := by ring

-- 最大角为 90 - m/2，由 m > 0 得到它严格小于 90。
theorem acuteWithMin_isAcute (m : ℝ) (hm0 : 0 < m) (hm60 : m ≤ 60) :
    Acute (acuteWithMin m hm0 hm60) := by
  apply (acute_iff_max (acuteWithMin m hm0 hm60)).2
  change 90 - m / 2 < 90
  linarith

-- 对任意 0 < m ≤ 45，构造最小角为 m 的直角三角形。
def rightWithMin (m : ℝ) (hm0 : 0 < m) (hm45 : m ≤ 45) : Triangle where
  a := m
  b := 90 - m
  c := 90
  a_pos := hm0
  ab := by linarith
  bc := by linarith
  angle_sum := by ring

-- 最大角按构造等于 90。
theorem rightWithMin_isRight (m : ℝ) (hm0 : 0 < m) (hm45 : m ≤ 45) :
    Right (rightWithMin m hm0 hm45) := by
  apply (right_iff_max (rightWithMin m hm0 hm45)).2
  rfl

-- 对任意 0 < m < 45，构造最小角为 m 的钝角三角形。
def obtuseWithMin (m : ℝ) (hm0 : 0 < m) (hm45 : m < 45) : Triangle where
  a := m
  b := m
  c := 180 - 2 * m
  a_pos := hm0
  ab := le_rfl
  bc := by linarith
  angle_sum := by ring

-- 最大角为 180 - 2m，由 m < 45 得到它严格大于 90。
theorem obtuseWithMin_isObtuse (m : ℝ) (hm0 : 0 < m) (hm45 : m < 45) :
    Obtuse (obtuseWithMin m hm0 hm45) := by
  apply (obtuse_iff_max (obtuseWithMin m hm0 hm45)).2
  change 90 < 180 - 2 * m
  linarith

-- “存在一个最小角为 m 的锐角三角形”的准确充要条件。
theorem acute_min_exists_iff (m : ℝ) :
    (∃ t : Triangle, Acute t ∧ t.a = m) ↔ 0 < m ∧ m ≤ 60 := by
  constructor
  · rintro ⟨t, _hAcute, ha⟩
    -- 任意三角形的最小角均属于 (0, 60]。
    have hr := min_range t
    simpa only [ha] using hr
  · rintro ⟨hm0, hm60⟩
    -- 显式给出三角形，并验证锐角性质与最小角数值。
    exact ⟨acuteWithMin m hm0 hm60, acuteWithMin_isAcute m hm0 hm60, rfl⟩

-- “存在一个最小角为 m 的直角三角形”的准确充要条件。
theorem right_min_exists_iff (m : ℝ) :
    (∃ t : Triangle, Right t ∧ t.a = m) ↔ 0 < m ∧ m ≤ 45 := by
  constructor
  · rintro ⟨t, hRight, ha⟩
    have hr := right_min_range t hRight
    simpa only [ha] using hr
  · rintro ⟨hm0, hm45⟩
    exact ⟨rightWithMin m hm0 hm45, rightWithMin_isRight m hm0 hm45, rfl⟩

-- “存在一个最小角为 m 的钝角三角形”的准确充要条件。
theorem obtuse_min_exists_iff (m : ℝ) :
    (∃ t : Triangle, Obtuse t ∧ t.a = m) ↔ 0 < m ∧ m < 45 := by
  constructor
  · rintro ⟨t, hObtuse, ha⟩
    have hr := obtuse_min_range t hObtuse
    simpa only [ha] using hr
  · rintro ⟨hm0, hm45⟩
    exact ⟨obtuseWithMin m hm0 hm45, obtuseWithMin_isObtuse m hm0 hm45, rfl⟩

-- 对每一个实数 m ∈ (0, 45)，确实分别存在三种类型的三角形。
-- 这证明整个区间的结论，而不是只验证 m = 30 的一个样本。
theorem all_three_types_possible (m : ℝ) (hm0 : 0 < m) (hm45 : m < 45) :
    (∃ t : Triangle, Acute t ∧ t.a = m) ∧
    (∃ t : Triangle, Right t ∧ t.a = m) ∧
    (∃ t : Triangle, Obtuse t ∧ t.a = m) := by
  refine ⟨?_, ?_, ?_⟩
  · apply (acute_min_exists_iff m).2
    exact ⟨hm0, by linarith⟩
  · apply (right_min_exists_iff m).2
    exact ⟨hm0, le_of_lt hm45⟩
  · exact (obtuse_min_exists_iff m).2 ⟨hm0, hm45⟩

-- 先限制 m 为实际可取的最小角，避免“没有三角形”导致全称命题空真。
-- 该定理准确表达：只知道最小角 m，能够保证锐角，当且仅当 m > 45。
theorem guarantees_acute_iff (m : ℝ) (hm0 : 0 < m) (_hm60 : m ≤ 60) :
    (∀ t : Triangle, t.a = m → Acute t) ↔ 45 < m := by
  constructor
  · intro hAll
    by_contra hNot
    have hm45 : m ≤ 45 := le_of_not_gt hNot
    -- 若 m ≤ 45，构造最小角为 m 的直角三角形，与“全部锐角”矛盾。
    have hAcute := hAll (rightWithMin m hm0 hm45) rfl
    have hlt := (acute_iff_max (rightWithMin m hm0 hm45)).1 hAcute
    change (90 : ℝ) < 90 at hlt
    linarith
  · intro hm45 t ha
    -- 若 m > 45，任何最小角为 m 的三角形都满足此前的充分条件。
    apply min_gt_45_acute t
    rw [ha]
    exact hm45

-- 对每一个可行的最小角 m，均不能保证所有对应三角形都是直角三角形。
theorem no_min_guarantees_right (m : ℝ) (hm0 : 0 < m) (hm60 : m ≤ 60) :
    ¬ (∀ t : Triangle, t.a = m → Right t) := by
  intro hAll
  -- 取同样具有最小角 m 的锐角三角形作为反例。
  have hRight := hAll (acuteWithMin m hm0 hm60) rfl
  have hAcute := acuteWithMin_isAcute m hm0 hm60
  have hlt := (acute_iff_max (acuteWithMin m hm0 hm60)).1 hAcute
  have heq := (right_iff_max (acuteWithMin m hm0 hm60)).1 hRight
  linarith

-- 对每一个可行的最小角 m，均不能保证所有对应三角形都是钝角三角形。
theorem no_min_guarantees_obtuse (m : ℝ) (hm0 : 0 < m) (hm60 : m ≤ 60) :
    ¬ (∀ t : Triangle, t.a = m → Obtuse t) := by
  intro hAll
  have hObtuse := hAll (acuteWithMin m hm0 hm60) rfl
  have hAcute := acuteWithMin_isAcute m hm0 hm60
  have hlt := (acute_iff_max (acuteWithMin m hm0 hm60)).1 hAcute
  have hgt := (obtuse_iff_max (acuteWithMin m hm0 hm60)).1 hObtuse
  linarith

end TriangleAngleLogic

/-! ## 8. 检查原有 32 个定理依赖的公理 -/

#print axioms TriangleAngleLogic.min_range
#print axioms TriangleAngleLogic.max_range
#print axioms TriangleAngleLogic.acute_iff_max
#print axioms TriangleAngleLogic.right_iff_max
#print axioms TriangleAngleLogic.obtuse_iff_max
#print axioms TriangleAngleLogic.acute_iff_max_range
#print axioms TriangleAngleLogic.obtuse_iff_max_range
#print axioms TriangleAngleLogic.acute_min_range
#print axioms TriangleAngleLogic.right_min_range
#print axioms TriangleAngleLogic.obtuse_min_range
#print axioms TriangleAngleLogic.min_gt_45_acute
#print axioms TriangleAngleLogic.min_eq_45_acute_or_right
#print axioms TriangleAngleLogic.min_ge_45_not_obtuse
#print axioms TriangleAngleLogic.three_types_at_30
#print axioms TriangleAngleLogic.two_types_at_45
#print axioms TriangleAngleLogic.not_every_acute_has_min_gt_45
#print axioms TriangleAngleLogic.min_le_60_does_not_force_acute
#print axioms TriangleAngleLogic.min_le_45_does_not_force_right
#print axioms TriangleAngleLogic.min_lt_45_does_not_force_obtuse
#print axioms TriangleAngleLogic.min_lt_45_does_not_force_acute
#print axioms TriangleAngleLogic.min_eq_45_does_not_force_acute
#print axioms TriangleAngleLogic.min_eq_45_does_not_force_right
#print axioms TriangleAngleLogic.acuteWithMin_isAcute
#print axioms TriangleAngleLogic.rightWithMin_isRight
#print axioms TriangleAngleLogic.obtuseWithMin_isObtuse
#print axioms TriangleAngleLogic.acute_min_exists_iff
#print axioms TriangleAngleLogic.right_min_exists_iff
#print axioms TriangleAngleLogic.obtuse_min_exists_iff
#print axioms TriangleAngleLogic.all_three_types_possible
#print axioms TriangleAngleLogic.guarantees_acute_iff
#print axioms TriangleAngleLogic.no_min_guarantees_right
#print axioms TriangleAngleLogic.no_min_guarantees_obtuse

namespace TriangleAngleLogic

/-!
## 9. 只知道任意一个内角

这里的 x 是题目给出的角度数。原模型中的 a、b、c 已按大小排列，
所以“其中一个角是 x”必须写成三个位置的析取，不能写成 t.a = x。
所有角度仍用实数表示，单位为度。
-/

def HasAngle (t : Triangle) (x : ℝ) : Prop :=
  t.a = x ∨ t.b = x ∨ t.c = x

-- 无论给出的是哪个位置的角，它都严格介于 0 与 180 之间。
theorem hasAngle_bounds (t : Triangle) (x : ℝ)
    (hx : HasAngle t x) : 0 < x ∧ x < 180 := by
  rcases hx with hx | hx | hx
  · constructor <;> linarith [t.a_pos, t.ab, t.bc, t.angle_sum]
  · constructor <;> linarith [t.a_pos, t.ab, t.bc, t.angle_sum]
  · constructor <;> linarith [t.a_pos, t.ab, t.bc, t.angle_sum]

-- “含有一个 90 度的角”与直角类型的定义完全一致。
theorem hasAngle_ninety_iff_right (t : Triangle) :
    HasAngle t 90 ↔ Right t := by
  rfl

-- 只要已知角大于 90 度，它就直接见证了钝角类型。
theorem hasAngle_gt_ninety_obtuse (t : Triangle) (x : ℝ)
    (hx : HasAngle t x) (hgt : 90 < x) : Obtuse t := by
  rcases hx with hx | hx | hx
  · exact Or.inl (by linarith)
  · exact Or.inr (Or.inl (by linarith))
  · exact Or.inr (Or.inr (by linarith))

-- 在锐角三角形中，任意被指出的一个角都小于 90 度。
theorem acute_hasAngle_lt_ninety (t : Triangle) (x : ℝ)
    (hA : Acute t) (hx : HasAngle t x) : x < 90 := by
  rcases hx with hx | hx | hx
  · linarith [hA.1]
  · linarith [hA.2.1]
  · linarith [hA.2.2]

-- 直角类型与钝角类型不可能同时成立。
theorem right_excludes_obtuse (t : Triangle) (hR : Right t) :
    ¬ Obtuse t := by
  have hc : t.c = 90 := (right_iff_max t).mp hR
  intro hO
  rcases hO with hO | hO | hO
  · linarith [t.ab, t.bc]
  · linarith [t.bc]
  · linarith

/-!
## 10. 把任意次序的三个角放入有序模型

输入 x、y、z 均为正且和为 180。下面按三个数的大小选取六种排列之一。
这一步仅改变存放位置，不改变三个角及其类型。
noncomputable 来自实数比较，并不省略任何证明义务。
-/

noncomputable def ofAngles (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = 180) : Triangle :=
  if hxy : x ≤ y then
    if hyz : y ≤ z then
      { a := x, b := y, c := z,
        a_pos := hx, ab := hxy, bc := hyz, angle_sum := hs }
    else if hxz : x ≤ z then
      { a := x, b := z, c := y,
        a_pos := hx, ab := hxz, bc := by linarith,
        angle_sum := by linarith }
    else
      { a := z, b := x, c := y,
        a_pos := hz, ab := by linarith, bc := hxy,
        angle_sum := by linarith }
  else
    if hxz : x ≤ z then
      { a := y, b := x, c := z,
        a_pos := hy, ab := by linarith, bc := hxz,
        angle_sum := by linarith }
    else if hyz : y ≤ z then
      { a := y, b := z, c := x,
        a_pos := hy, ab := hyz, bc := by linarith,
        angle_sum := by linarith }
    else
      { a := z, b := y, c := x,
        a_pos := hz, ab := by linarith, bc := by linarith,
        angle_sum := by linarith }

-- 六种排列中，原来的三个角都仍然属于构造出的三角形。
theorem ofAngles_hasAngles (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = 180) :
    HasAngle (ofAngles x y z hx hy hz hs) x ∧
    HasAngle (ofAngles x y z hx hy hz hs) y ∧
    HasAngle (ofAngles x y z hx hy hz hs) z := by
  unfold ofAngles
  split_ifs <;> simp [HasAngle]

-- 三个原始角均小于 90 时，排序后的三角形也为锐角类型。
theorem ofAngles_isAcute (x y z : ℝ)
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hs : x + y + z = 180)
    (hx90 : x < 90) (hy90 : y < 90) (hz90 : z < 90) :
    Acute (ofAngles x y z hx hy hz hs) := by
  unfold ofAngles
  split_ifs <;> simp_all [Acute]

/-!
## 11. 任意一个给定锐角的三种通用构造

对每个 0 < x < 90：
锐角构造为 (x, 90 - x/2, 90 - x/2)；
直角构造为 (x, 90 - x, 90)；
钝角构造为 (x, 45 - x/2, 135 - x/2)。
ofAngles 自动排序；不能把这些原始顺序直接当作最小、中间、最大角。
-/

noncomputable def acuteWithAngle (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : Triangle :=
  ofAngles x (90 - x / 2) (90 - x / 2)
    hx0 (by linarith) (by linarith) (by ring)

theorem acuteWithAngle_hasAngle (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : HasAngle (acuteWithAngle x hx0 hx90) x := by
  unfold acuteWithAngle
  exact (ofAngles_hasAngles _ _ _ _ _ _ _).1

theorem acuteWithAngle_isAcute (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : Acute (acuteWithAngle x hx0 hx90) := by
  unfold acuteWithAngle
  apply ofAngles_isAcute <;> linarith

noncomputable def rightWithAngle (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : Triangle :=
  ofAngles x (90 - x) 90
    hx0 (by linarith) (by norm_num) (by ring)

theorem rightWithAngle_hasAngle (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : HasAngle (rightWithAngle x hx0 hx90) x := by
  unfold rightWithAngle
  exact (ofAngles_hasAngles _ _ _ _ _ _ _).1

theorem rightWithAngle_isRight (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : Right (rightWithAngle x hx0 hx90) := by
  change HasAngle (rightWithAngle x hx0 hx90) 90
  unfold rightWithAngle
  exact (ofAngles_hasAngles _ _ _ _ _ _ _).2.2

noncomputable def obtuseWithAcuteAngle (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : Triangle :=
  ofAngles x (45 - x / 2) (135 - x / 2)
    hx0 (by linarith) (by linarith) (by ring)

theorem obtuseWithAcuteAngle_hasAngle (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : HasAngle (obtuseWithAcuteAngle x hx0 hx90) x := by
  unfold obtuseWithAcuteAngle
  exact (ofAngles_hasAngles _ _ _ _ _ _ _).1

theorem obtuseWithAcuteAngle_isObtuse (x : ℝ) (hx0 : 0 < x)
    (hx90 : x < 90) : Obtuse (obtuseWithAcuteAngle x hx0 hx90) := by
  apply hasAngle_gt_ninety_obtuse _ (135 - x / 2)
  · unfold obtuseWithAcuteAngle
    exact (ofAngles_hasAngles _ _ _ _ _ _ _).2.2
  · linarith

-- 给定的角本身为钝角时，另外两个角取为相等的正角。
noncomputable def obtuseWithObtuseAngle (x : ℝ) (hx90 : 90 < x)
    (hx180 : x < 180) : Triangle :=
  ofAngles x ((180 - x) / 2) ((180 - x) / 2)
    (by linarith) (by linarith) (by linarith) (by ring)

theorem obtuseWithObtuseAngle_hasAngle (x : ℝ) (hx90 : 90 < x)
    (hx180 : x < 180) : HasAngle (obtuseWithObtuseAngle x hx90 hx180) x := by
  unfold obtuseWithObtuseAngle
  exact (ofAngles_hasAngles _ _ _ _ _ _ _).1

theorem obtuseWithObtuseAngle_isObtuse (x : ℝ) (hx90 : 90 < x)
    (hx180 : x < 180) : Obtuse (obtuseWithObtuseAngle x hx90 hx180) := by
  exact hasAngle_gt_ninety_obtuse _ x
    (obtuseWithObtuseAngle_hasAngle x hx90 hx180) hx90

/-!
## 12. 给定任意一个角时，各类型存在的精确范围

注意直角三角形中“任意一个角”的可能范围为 (0, 90]；
它可以是锐角，也可以恰好是直角。
钝角三角形中“任意一个角”可能是锐角或钝角，但不能为 90。
-/

theorem acute_angle_exists_iff (x : ℝ) :
    (∃ t : Triangle, Acute t ∧ HasAngle t x) ↔ 0 < x ∧ x < 90 := by
  constructor
  · rintro ⟨t, hA, hx⟩
    exact ⟨(hasAngle_bounds t x hx).1, acute_hasAngle_lt_ninety t x hA hx⟩
  · rintro ⟨hx0, hx90⟩
    exact ⟨acuteWithAngle x hx0 hx90, acuteWithAngle_isAcute x hx0 hx90,
      acuteWithAngle_hasAngle x hx0 hx90⟩

theorem right_angle_exists_iff (x : ℝ) :
    (∃ t : Triangle, Right t ∧ HasAngle t x) ↔ 0 < x ∧ x ≤ 90 := by
  constructor
  · rintro ⟨t, hR, hx⟩
    refine ⟨(hasAngle_bounds t x hx).1, ?_⟩
    have hc : t.c = 90 := (right_iff_max t).mp hR
    rcases hx with hx | hx | hx <;> linarith [t.ab, t.bc]
  · rintro ⟨hx0, hx90⟩
    rcases lt_or_eq_of_le hx90 with hlt | heq
    · exact ⟨rightWithAngle x hx0 hlt, rightWithAngle_isRight x hx0 hlt,
        rightWithAngle_hasAngle x hx0 hlt⟩
    · subst x
      let t := rightWithAngle 45 (by norm_num) (by norm_num)
      have hR : Right t := rightWithAngle_isRight 45 (by norm_num) (by norm_num)
      exact ⟨t, hR, (hasAngle_ninety_iff_right t).mpr hR⟩

theorem obtuse_angle_exists_iff (x : ℝ) :
    (∃ t : Triangle, Obtuse t ∧ HasAngle t x) ↔
      (0 < x ∧ x < 90) ∨ (90 < x ∧ x < 180) := by
  constructor
  · rintro ⟨t, hO, hx⟩
    have hb := hasAngle_bounds t x hx
    rcases lt_trichotomy x 90 with hlt | heq | hgt
    · exact Or.inl ⟨hb.1, hlt⟩
    · subst x
      exact False.elim (right_excludes_obtuse t
        ((hasAngle_ninety_iff_right t).mp hx) hO)
    · exact Or.inr ⟨hgt, hb.2⟩
  · rintro (⟨hx0, hx90⟩ | ⟨hx90, hx180⟩)
    · exact ⟨obtuseWithAcuteAngle x hx0 hx90,
        obtuseWithAcuteAngle_isObtuse x hx0 hx90,
        obtuseWithAcuteAngle_hasAngle x hx0 hx90⟩
    · exact ⟨obtuseWithObtuseAngle x hx90 hx180,
        obtuseWithObtuseAngle_isObtuse x hx90 hx180,
        obtuseWithObtuseAngle_hasAngle x hx90 hx180⟩

-- 这个存在性结论排除了不可行角度造成的全称命题“空真”。
theorem angle_exists_iff (x : ℝ) :
    (∃ t : Triangle, HasAngle t x) ↔ 0 < x ∧ x < 180 := by
  constructor
  · rintro ⟨t, hx⟩
    exact hasAngle_bounds t x hx
  · rintro ⟨hx0, hx180⟩
    by_cases hx90 : x ≤ 90
    · obtain ⟨t, _, hx⟩ := (right_angle_exists_iff x).mpr ⟨hx0, hx90⟩
      exact ⟨t, hx⟩
    · obtain ⟨t, _, hx⟩ := (obtuse_angle_exists_iff x).mpr
        (Or.inr ⟨by linarith, hx180⟩)
      exact ⟨t, hx⟩

-- 三个存在命题各有自己的见证，不是同一个三角形兼有三种类型。
theorem all_three_types_possible_for_angle (x : ℝ)
    (hx0 : 0 < x) (hx90 : x < 90) :
    (∃ t : Triangle, Acute t ∧ HasAngle t x) ∧
    (∃ t : Triangle, Right t ∧ HasAngle t x) ∧
    (∃ t : Triangle, Obtuse t ∧ HasAngle t x) := by
  exact ⟨(acute_angle_exists_iff x).mpr ⟨hx0, hx90⟩,
    (right_angle_exists_iff x).mpr ⟨hx0, le_of_lt hx90⟩,
    (obtuse_angle_exists_iff x).mpr (Or.inl ⟨hx0, hx90⟩)⟩

/-!
## 13. “仅凭这一个角就一定如此”的精确判定

这里的全称量词遍历所有含角 x 的三角形。
必须先限定 0 < x < 180，确保确有这样的三角形。
-/

theorem no_angle_guarantees_acute (x : ℝ)
    (hx0 : 0 < x) (hx180 : x < 180) :
    ¬ (∀ t : Triangle, HasAngle t x → Acute t) := by
  intro h
  by_cases hx90 : x < 90
  · let t := rightWithAngle x hx0 hx90
    have hR : Right t := rightWithAngle_isRight x hx0 hx90
    have hA : Acute t := h t (rightWithAngle_hasAngle x hx0 hx90)
    have hc : t.c = 90 := (right_iff_max t).mp hR
    linarith [hA.2.2]
  · obtain ⟨t, ht⟩ := (angle_exists_iff x).mpr ⟨hx0, hx180⟩
    have hlt := acute_hasAngle_lt_ninety t x (h t ht) ht
    exact hx90 hlt

theorem angle_guarantees_right_iff (x : ℝ)
    (hx0 : 0 < x) (hx180 : x < 180) :
    (∀ t : Triangle, HasAngle t x → Right t) ↔ x = 90 := by
  constructor
  · intro h
    rcases lt_trichotomy x 90 with hlt | heq | hgt
    · obtain ⟨t, hO, ht⟩ := (obtuse_angle_exists_iff x).mpr
        (Or.inl ⟨hx0, hlt⟩)
      exact False.elim (right_excludes_obtuse t (h t ht) hO)
    · exact heq
    · obtain ⟨t, hO, ht⟩ := (obtuse_angle_exists_iff x).mpr
        (Or.inr ⟨hgt, hx180⟩)
      exact False.elim (right_excludes_obtuse t (h t ht) hO)
  · intro heq t ht
    subst x
    exact (hasAngle_ninety_iff_right t).mp ht

theorem angle_guarantees_obtuse_iff (x : ℝ)
    (hx0 : 0 < x) (_hx180 : x < 180) :
    (∀ t : Triangle, HasAngle t x → Obtuse t) ↔ 90 < x := by
  constructor
  · intro h
    by_contra hn
    have hx90 : x ≤ 90 := by linarith
    obtain ⟨t, hR, ht⟩ := (right_angle_exists_iff x).mpr ⟨hx0, hx90⟩
    exact right_excludes_obtuse t hR (h t ht)
  · intro hgt t ht
    exact hasAngle_gt_ninety_obtuse t x ht hgt

/-!
## 14. 一个 60 度的角：三种明确反例

三个三角形分别按大小写成 (60,60,60)、(30,60,90)、(20,60,100)。
都含 60 度，但类型不同，因此不能把“一个角”偷换成“最小角”。
-/

def acuteAngle60 : Triangle where
  a := 60
  b := 60
  c := 60
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

def rightAngle60 : Triangle where
  a := 30
  b := 60
  c := 90
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

def obtuseAngle60 : Triangle where
  a := 20
  b := 60
  c := 100
  a_pos := by norm_num
  ab := by norm_num
  bc := by norm_num
  angle_sum := by norm_num

theorem three_types_at_60_angle :
    (Acute acuteAngle60 ∧ HasAngle acuteAngle60 60) ∧
    (Right rightAngle60 ∧ HasAngle rightAngle60 60) ∧
    (Obtuse obtuseAngle60 ∧ HasAngle obtuseAngle60 60) := by
  norm_num [Acute, Right, Obtuse, HasAngle,
    acuteAngle60, rightAngle60, obtuseAngle60]

-- 错误全称命题的否定；并非断言所有含锐角的三角形都不锐。
theorem one_acute_angle_does_not_force_acute :
    ¬ (∀ t : Triangle, ∀ x : ℝ,
      HasAngle t x → 0 < x → x < 90 → Acute t) := by
  intro h
  have hA : Acute rightAngle60 :=
    h rightAngle60 60 (by norm_num [HasAngle, rightAngle60])
      (by norm_num) (by norm_num)
  norm_num [Acute, rightAngle60] at hA

/-!
## 15. 新增定理的公理依赖检查

这些命令与原有 32 项一起接受实际编译检查。
没有 sorry、admit 或新增 axiom；公理名称不是错误提示。
-/

#print axioms hasAngle_bounds
#print axioms hasAngle_ninety_iff_right
#print axioms hasAngle_gt_ninety_obtuse
#print axioms acute_hasAngle_lt_ninety
#print axioms right_excludes_obtuse
#print axioms ofAngles_hasAngles
#print axioms ofAngles_isAcute
#print axioms acuteWithAngle_hasAngle
#print axioms acuteWithAngle_isAcute
#print axioms rightWithAngle_hasAngle
#print axioms rightWithAngle_isRight
#print axioms obtuseWithAcuteAngle_hasAngle
#print axioms obtuseWithAcuteAngle_isObtuse
#print axioms obtuseWithObtuseAngle_hasAngle
#print axioms obtuseWithObtuseAngle_isObtuse
#print axioms acute_angle_exists_iff
#print axioms right_angle_exists_iff
#print axioms obtuse_angle_exists_iff
#print axioms angle_exists_iff
#print axioms all_three_types_possible_for_angle
#print axioms no_angle_guarantees_acute
#print axioms angle_guarantees_right_iff
#print axioms angle_guarantees_obtuse_iff
#print axioms three_types_at_60_angle
#print axioms one_acute_angle_does_not_force_acute

end TriangleAngleLogic
