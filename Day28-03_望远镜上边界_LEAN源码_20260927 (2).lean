import Mathlib

/-! ================================================================
   偏元数学 · Day28-03 · 动作上链与和乐 · 望远镜（上边界量）
   ------------------------------------------------------------------
   核心：凡能写成"端点差"的量（上边界型），沿任何回到起点的路径，其和必为 0。
         这是经典"伸缩求和"，也是本仓判别的对照物：
         我们的动作量 Σδ 不满足它（→ Day28-04 / Day28-06）。
   本稿范围：两定理
     定理1  boundary_telescope    : Σ (f(x_{i+1}) − f(x_i)) = f(x_N) − f(x_0)
     定理2  boundary_closed_zero  : 若 x_N = x_0，则该和 = 0
   不做：不涉及 ℂ / 拓扑（纯 ℝ 上的有限和）。
   注：本件不依赖 F，独立可提交。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ----------------------------------------------------------------
   ⚠️ 记法：本件【不用 ∑ 记法】，直接写 Finset.sum —— 绕开 BigOperators scope 问题。
      若 Finset.sum_range_succ 报错，备选名见文末注释。
   ================================================================ -/

namespace PrenaryDay28C

/-- 定理1（望远镜 / 伸缩求和）：上边界量沿有限路径之和 = 端点差 -/
theorem boundary_telescope {α : Type*} (f : α → ℝ) (x : ℕ → α) (N : ℕ) :
    (Finset.range N).sum (fun i => f (x (i+1)) - f (x i)) = f (x N) - f (x 0) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- 定理2（闭路 ⟹ 上边界量之和为 0） -/
theorem boundary_closed_zero {α : Type*} (f : α → ℝ) (x : ℕ → α) (N : ℕ)
    (hclosed : x N = x 0) :
    (Finset.range N).sum (fun i => f (x (i+1)) - f (x i)) = 0 := by
  rw [boundary_telescope, hclosed, sub_self]

end PrenaryDay28C

/- ----------------------------------------------------------------
   若 Finset.sum_range_succ 报错，依次试：
     Finset.sum_range_succ'      （有些版本带撇）
     Finset.range_succ 之后再 simp
   若仍不通，可改成对 Nat 归纳 + Finset.sum_insert（较繁），或告诉我报错原文。
   ---------------------------------------------------------------- -/
