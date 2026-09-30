import Mathlib

/-! ================================================================
   偏元数学 · Day28-22 · 复缩放的显式刻画·收口（§8.6 待达项 1）
   ------------------------------------------------------------------
   缘起：S-006 V1.2（S-006）§8.6 待达 "复缩放的显式刻画（λ = |λ|·e^{i·arg λ}）"。
        Day28-21（极式分拆，把极式当假设）已给前三面；
        本件补上那座"桥"：复数的极式复原，从而把 §8.6 的字面口径补全。
     定理A  prenary_norm_mul_exp_arg : (‖w‖ : ℂ) * exp (arg w * I) = w
     定理B  prenary_cscale_arg_form : w * z = (‖w‖ : ℂ) * exp (arg w * I) * z
   桥引理：Complex.norm_mul_exp_arg_mul_I（Mathlib 自带，无前提条件）。
   不做：不做 §10 的一般和乐（已另件）；不主张本件即"复缩放"的完整理论。
   注：本件自带所需定义，独立可提交。上承 Day28-08、-09、-10、-21（缩放四件）。
   日期：2026-09-29
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28T

/-- 复缩放：乘一个非零复数（`w` 为缩放因子、`z` 为被作用的对象）。 -/
def cscale (w z : ℂ) : ℂ := w * z

/-- 定理A（极式复原／那座桥）：复数的模与幅角复原它本身（对全体 ℂ 成立）。 -/
theorem prenary_norm_mul_exp_arg (w : ℂ) :
    (‖w‖ : ℂ) * Complex.exp (Complex.arg w * Complex.I) = w := by
  exact Complex.norm_mul_exp_arg_mul_I w

/-- 定理B（显式刻画）：把缩放因子写成 `w = ‖w‖·e^{i·arg w}`，
    则复缩放 ＝ 实缩放（乘 `‖w‖`）∘ 旋转（乘 `e^{i·arg w}`）。 -/
theorem prenary_cscale_arg_form (w z : ℂ) :
    cscale w z = (‖w‖ : ℂ) * Complex.exp (Complex.arg w * Complex.I) * z := by
  simp only [cscale]
  rw [prenary_norm_mul_exp_arg w]

end PrenaryDay28T
