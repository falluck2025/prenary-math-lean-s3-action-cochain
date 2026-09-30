import Mathlib

/-! ================================================================
   偏元数学 · Day28-10 · 缩放那一支 · 补量-乘法同构与对数可加性
   ------------------------------------------------------------------
   核心：Day28-01 的 F 其"补量形式"是乘性的（c − F = (c−x)(c−y)/c）——
         本件把它讲透：① 归一化补量 φ(x) = (c−x)/c 下，F 就是普通乘法；
                       ② 取对数后，F 就是加法。
         这就是"缩放（乘性）↔ 加性"的那座桥，也是"缩放那一支"的代数目击。
   本稿范围：两定理
     定理1  F_complement_mul : (c − F x y c)/c = ((c−x)/c) * ((c−y)/c)
     定理2  F_complement_log : log((c − F x y c)/c)
                             = log((c−x)/c) + log((c−y)/c)     （需 c≠x, c≠y）
   不做：不涉及 ℂ（本件纯 ℝ）；不主张"缩放构成二态"；不主张 log 与熵的对应成立。
   注：本件自带 F 的定义，独立可提交。上承 Day28-01（F 的代数）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28I

/-- 残差层不变区间上的保区间运算：F(x,y;c) = x + y − x*y/c
    ⚠️ 必须标 noncomputable：`x*y/c` 依赖 `Real.instDivInvMonoid`（noncomputable） -/
noncomputable def F (x y c : ℝ) : ℝ := x + y - x*y/c

/-- 定理1（补量-乘法同构）：归一化补量 φ(x) = (c−x)/c 下，F 就是乘法 -/
theorem F_complement_mul (x y c : ℝ) (hc : c ≠ 0) :
    (c - F x y c) / c = ((c - x)/c) * ((c - y)/c) := by
  unfold F
  field_simp
  ring

/-- 定理2（对数可加性）：取对数后，F 就是加法 —— "乘性 ↔ 加性"的桥 -/
theorem F_complement_log (x y c : ℝ) (hc : c ≠ 0) (hx : c ≠ x) (hy : c ≠ y) :
    Real.log ((c - F x y c) / c)
      = Real.log ((c - x)/c) + Real.log ((c - y)/c) := by
  rw [F_complement_mul x y c hc, Real.log_mul]
  · exact div_ne_zero (sub_ne_zero.mpr hx) hc
  · exact div_ne_zero (sub_ne_zero.mpr hy) hc

end PrenaryDay28I
