import Mathlib

/-! ================================================================
   偏元数学 · Day28-12 · 缩放那一支 · 归一化残差与补量
   ------------------------------------------------------------------
   核心：把"残差与上界的比值"这个量摆到明处 ——
         归一化残差 x/c 落在 (0,1)；而 F 的补量 φ(x) = (c−x)/c 恰等于 1 − x/c，
         即"补量"与"归一化残差"互补为 1。
         该比值是"量的偏好"候选 A／②的共同语言（区间余量 / 权重比值）。
   本稿范围：三定理
     定理1  prenary_phi_eq             : (c−x)/c = 1 − x/c
     定理2  prenary_normalized_in_Ioo  : 0<x<c ⟹ x/c ∈ (0,1)
     定理3  prenary_phi_in_Ioo         : 0<x<c ⟹ φ(x) ∈ (0,1)
   不做：不涉及物理侧的 η（本件纯数学）；不主张"权重 ∝ 归一化残差"成立。
   注：本件自带所需引理，独立可提交。上承 Day28-10（补量-乘法同构）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28K

/-- 定理1（补量即"1 − 归一化残差"）：(c−x)/c = 1 − x/c -/
theorem prenary_phi_eq (x c : ℝ) (hc : c ≠ 0) :
    (c - x) / c = 1 - x / c := by
  field_simp
  ring

/-- 定理2（归一化残差落在 (0,1)）：0<x<c ⟹ 0 < x/c ∧ x/c < 1 -/
theorem prenary_normalized_in_Ioo (x c : ℝ) (hx : 0 < x) (hxc : x < c) :
    0 < x / c ∧ x / c < 1 := by
  have hc : 0 < c := by linarith
  have hmul : x / c * c = x := by field_simp [ne_of_gt hc]
  constructor
  · positivity
  · nlinarith [hmul, hxc, hc, hx]

/-- 定理3（补量落在 (0,1)）：0<x<c ⟹ 0 < φ(x) < 1 -/
theorem prenary_phi_in_Ioo (x c : ℝ) (hx : 0 < x) (hxc : x < c) :
    0 < (c - x) / c ∧ (c - x) / c < 1 := by
  have hc : 0 < c := by linarith
  have h := prenary_normalized_in_Ioo x c hx hxc
  have heq : (c - x) / c = 1 - x / c := by
    field_simp
    ring
  rw [heq]
  constructor <;> linarith [h.1, h.2]

end PrenaryDay28K
