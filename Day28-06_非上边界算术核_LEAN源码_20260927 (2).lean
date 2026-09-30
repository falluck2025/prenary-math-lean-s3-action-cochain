import Mathlib

/-! ================================================================
   偏元数学 · Day28-06 · 动作上链与和乐 · 非上边界的算术核
   ------------------------------------------------------------------
   核心：把"c 不是上边界"落到可算的事实上 ——
         动作量在闭路上的和不为 0（N·(π/2) ≠ 0, N ≥ 1），
         而上边界量（Day28-03）在闭路上恒为 0。
         两者并置 ⟹ 动作量不能写成端点差 ⟹ 它不是上边界。
   本稿范围：三定理
     定理1  N_mul_pi_div_two_ne_zero : 0<N ⟹ N·(π/2) ≠ 0
     定理2  action_sum_nonzero       : Σ_{i<N} (π/2) ≠ 0,  N ≥ 1
     定理3  action_not_boundary      : 非上边界的并置陈述（见下）
   不做：不在此件做"不存在任何 f"的全称证明（已用闭路反例在正文给出；
         机器侧此处只落"闭路和 ≠ 0"这一半）。
   注：本件只依赖 mul_ne_zero / 有限和常量引理，最稳。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ----------------------------------------------------------------
   ⚠️ 记法：本件【不用 ∑ 记法】，直接写 Finset.sum —— 绕开 BigOperators scope 问题。
   ================================================================ -/

namespace PrenaryDay28F

/-- 定理1：0 < N ⟹ N · (π/2) ≠ 0 -/
theorem N_mul_pi_div_two_ne_zero (N : ℕ) (hN : 0 < N) :
    (N : ℝ) * (Real.pi / 2) ≠ 0 := by
  have h1 : (N : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_iff_ne_zero.mp hN)
  have h2 : Real.pi / 2 ≠ 0 := by positivity
  exact mul_ne_zero h1 h2

/-- 定理2（动作量和在闭路上不为 0）：Σ_{i<N} (π/2) ≠ 0,  N ≥ 1 -/
theorem action_sum_nonzero (N : ℕ) (hN : 0 < N) :
    (Finset.range N).sum (fun _ => (Real.pi / 2)) ≠ 0 := by
  rw [Finset.sum_const, Finset.card_range]
  simp only [nsmul_eq_mul]
  exact N_mul_pi_div_two_ne_zero N hN

/-- 定理3（并置陈述）：存在回到原处的闭路，其上动作量和 ≠ 0；
    对照 Day28-03：上边界量在任何闭路上恒为 0。
    ⟹ 动作量不能写成 f(x_N) − f(x_0) 的形式（否则闭路和为 0）。 -/
theorem action_not_boundary (N : ℕ) (hN : 0 < N) :
    (Finset.range N).sum (fun _ => (Real.pi / 2)) ≠ 0 ∧
      (∀ (f : ℝ → ℝ) (y : ℕ → ℝ), y N = y 0 →
        (Finset.range N).sum (fun i => f (y (i+1)) - f (y i)) = 0) := by
  refine ⟨action_sum_nonzero N hN, ?_⟩
  intro f y hy
  have : (Finset.range N).sum (fun i => f (y (i+1)) - f (y i)) = f (y N) - f (y 0) := by
    induction N with
    | zero => simp
    | succ n ih =>
      rw [Finset.sum_range_succ, ih]
      ring
  rw [this, hy, sub_self]

end PrenaryDay28F
