import Mathlib

/-! ================================================================
   偏元数学 · Day28-01 · 动作上链与和乐 · F 的代数（残差层的保区间运算）
   ------------------------------------------------------------------
   核心：残差层不变区间 (0, δ₀) 上的保区间运算
         F(x,y;c) = x + y − x·y/c      等价于补量乘法：c − F = (c−x)(c−y)/c
         ① 基准固定时严格结合；② 基准随状态时，结合性差有精确公式。
   本稿范围：三定理
     定理1  F_assoc_defect : (a⊞b)⊞d − a⊞(b⊞d) = a·d·(c₂−c₁)/(c₁·c₂)
     定理2  F_assoc_same   : c₁ = c₂ 时严格结合（差为 0）
     定理3  F_complement   : c − F x y c = (c−x)(c−y)/c
   不做：不讨论 F 与"方向偏好 / δ₀ 不可达"的接口（属另一件）。
   注：本件自带 F 的定义，便于独立提交与比对。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ----------------------------------------------------------------
   ⚠️ 跑之前：本件未在本地编译过（写稿环境无 Lean）。
      若某条报错，请把错误信息贴回，我按报错改。
      定理1 若卡在 field_simp，备选写法见文末注释。
   ================================================================ -/

namespace PrenaryDay28A

/-- 残差层不变区间上的保区间运算：F(x,y;c) = x + y − x*y/c
    ⚠️ 必须标 noncomputable：`x*y/c` 用到 `Real.instDivInvMonoid`，该实例为 noncomputable -/
noncomputable def F (x y c : ℝ) : ℝ := x + y - x*y/c

/-- 定理1（结合性差的精确公式）：基准从 c₁ 变到 c₂ 所导致的非结合量 -/
theorem F_assoc_defect (a b d c₁ c₂ : ℝ) (h₁ : c₁ ≠ 0) (h₂ : c₂ ≠ 0) :
    F (F a b c₁) d c₂ - F a (F b d c₂) c₁ = a*d*(c₂-c₁)/(c₁*c₂) := by
  unfold F
  field_simp
  ring

/-- 定理2（基准相同时严格结合） -/
theorem F_assoc_same (a b d c : ℝ) (hc : c ≠ 0) :
    F (F a b c) d c = F a (F b d c) c := by
  unfold F
  field_simp
  ring

/-- 定理3（补量形式等价）：c − F x y c = (c−x)(c−y)/c -/
theorem F_complement (x y c : ℝ) (hc : c ≠ 0) :
    c - F x y c = (c-x)*(c-y)/c := by
  unfold F
  field_simp
  ring

end PrenaryDay28A

/- ----------------------------------------------------------------
   备选写法（若定理1 的 field_simp 报错）：先乘过分母，避开除法 ——

   theorem F_assoc_defect' (a b d c₁ c₂ : ℝ) :
       c₁*c₂*(F (F a b c₁) d c₂ - F a (F b d c₂) c₁) = a*d*(c₂-c₁) := by
     unfold F
     ring

   若再报错，试：field_simp [h₁, h₂]  （显式把非零假设交给 field_simp）

   解法1 的原理：F_assoc_defect 左边去分母后是同一件事，
                 乘过分母即"多项式恒等式"，ring 单独就能关闭。
   ---------------------------------------------------------------- -/
