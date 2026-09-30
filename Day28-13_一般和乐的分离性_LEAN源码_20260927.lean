import Mathlib

/-! ================================================================
   偏元数学 · Day28-13 · 一般和乐 · 分离性（角向 ⊕ 径向）
   ------------------------------------------------------------------
   核心：动作取复数形 λ = ρ·e^{iφ}（ρ > 0）；一般和乐 ＝ 各步之积 ∏λₙ。
         本件落定它的"分离性"：积 ＝ 模之积 · e^{i·角之和} ——
         即角向分量与径向分量可以拆开，这是"两个分量"的代数形式。
   本稿范围：三定理
     定理1  prenary_hol_two     : 两步分离性
     定理2  prenary_hol_three   : 三步分离性（由两步迭代而来）
     定理3  prenary_hol_ne_zero : 动作复数非零（对应 ε ∈ ℂ★）
   不做：不主张"一般和乐"具有物理意义；不引入 S¹ 的绕数（π₁）；
         不涉及"接入"；不主张 N 步的一般形式（本件给两步与三步的迭代型）。
   注：本件自带所需引理，独立可提交。上承 Day28-10（补量-乘法同构 · 乘法↔加法）。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28L

/-- 定理1（两步分离性）：两个动作复数之积 ＝ 模之积 · e^{i·角之和} -/
theorem prenary_hol_two (r s a b : ℝ) (hr : 0 < r) (hs : 0 < s) :
    (↑r * Complex.exp (↑a * Complex.I)) * (↑s * Complex.exp (↑b * Complex.I))
      = (↑(r * s)) * Complex.exp (↑(a + b) * Complex.I) := by
  have h : (↑(a + b) : ℂ) * Complex.I = ↑a * Complex.I + ↑b * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add]
  push_cast
  ring

/-- 定理2（三步分离性）：由定理1迭代两次得到，即"分离性可迭代" -/
theorem prenary_hol_three (r s t a b c : ℝ) (hr : 0 < r) (hs : 0 < s) (ht : 0 < t) :
    (↑r * Complex.exp (↑a * Complex.I)) * (↑s * Complex.exp (↑b * Complex.I))
        * (↑t * Complex.exp (↑c * Complex.I))
      = (↑(r * s * t)) * Complex.exp (↑(a + b + c) * Complex.I) := by
  rw [prenary_hol_two r s a b hr hs]
  rw [prenary_hol_two (r * s) t (a + b) c (by positivity) ht]
  push_cast
  ring

/-- 定理3（动作复数非零）：ρ > 0 ⟹ λ ≠ 0 —— 对应残差层的 ε ∈ ℂ★ -/
theorem prenary_hol_ne_zero (r a : ℝ) (hr : 0 < r) :
    (↑r * Complex.exp (↑a * Complex.I)) ≠ 0 := by
  apply mul_ne_zero
  · exact_mod_cast ne_of_gt hr
  · exact Complex.exp_ne_zero _

end PrenaryDay28L
