import Mathlib

/-! ================================================================
   偏元数学 · Day28-18 · 一般和乐 · 对数化（A2）
   ------------------------------------------------------------------
   核心：把"乘性累积"翻译成"加性累积"。一个关键设计判断：
         **不使用 Complex.log** —— 它的主值会把角压回 (−π, π]，
         从而抹掉"提升"，与本框架的"非上边界性"直接冲突
         （见备忘件：log 路的那堵墙）。
         改用**分两个分量**：模用 Real.log（单值、无分支问题）、
         角直接用 ℝ 提升（本来就在 ℝ 里，不需取对数）。
         本件把"对数化"写成一个映射 Λ，并落定它是
         "乘性合成 → 加法合成"的同态。
   本稿范围：一定义 ＋ 三定理
     定义   Lam               : Λ(ρ,φ) = (log ρ, φ)，值域 ℝ × ℝ
     定理1  prenary_lam_add   : 单步同态 Λ(ρ₁ρ₂, φ₁+φ₂) = Λ(ρ₁,φ₁) + Λ(ρ₂,φ₂)
     定理2  prenary_lam_three : 三步（由定理1迭代）
     定理3  prenary_lam_sum   : N 步（Finset.range / prod / sum）
   不做：不引入 Complex.log；不主张"角"有连续提升（提升是"沿序列"的
         性质，不是单个复数的性质）；不主张本件即"一般和乐"的完整理论。
   注：本件自带所需引理，独立可提交。
       上承 Day28-10（补量-乘法同构 · Real.log 可加）与 Day28-15（N 步分离性）。
   日期：2026-09-28
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28Q

/-- 对数化：单步动作 (ρ, φ) ↦ (log ρ, φ)，值域 ℝ × ℝ。
    ⚠️ 必须标 noncomputable：定义体含 Real.log -/
noncomputable def Lam (ρ φ : ℝ) : ℝ × ℝ := (Real.log ρ, φ)

/-- 定理1（单步同态）：Λ(ρ₁ρ₂, φ₁+φ₂) = Λ(ρ₁,φ₁) + Λ(ρ₂,φ₂) -/
theorem prenary_lam_add (ρ₁ ρ₂ φ₁ φ₂ : ℝ) (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂) :
    Lam (ρ₁ * ρ₂) (φ₁ + φ₂) = Lam ρ₁ φ₁ + Lam ρ₂ φ₂ := by
  have h : Real.log (ρ₁ * ρ₂) = Real.log ρ₁ + Real.log ρ₂ :=
    Real.log_mul (ne_of_gt h₁) (ne_of_gt h₂)
  unfold Lam
  rw [h]
  simp

/-- 定理2（三步）：Λ(ρ₁ρ₂ρ₃, φ₁+φ₂+φ₃) = Λ(ρ₁,φ₁) + Λ(ρ₂,φ₂) + Λ(ρ₃,φ₃) -/
theorem prenary_lam_three (ρ₁ ρ₂ ρ₃ φ₁ φ₂ φ₃ : ℝ)
    (h₁ : 0 < ρ₁) (h₂ : 0 < ρ₂) (h₃ : 0 < ρ₃) :
    Lam (ρ₁ * ρ₂ * ρ₃) (φ₁ + φ₂ + φ₃)
      = Lam ρ₁ φ₁ + Lam ρ₂ φ₂ + Lam ρ₃ φ₃ := by
  rw [prenary_lam_add (ρ₁ * ρ₂) ρ₃ (φ₁ + φ₂) φ₃ (mul_pos h₁ h₂) h₃]
  rw [prenary_lam_add ρ₁ ρ₂ φ₁ φ₂ h₁ h₂]

/-- 定理3（N 步）：Λ(∏ρ, Σφ) = Σ Λ(ρᵢ,φᵢ) -/
theorem prenary_lam_sum (N : ℕ) (ρ φ : ℕ → ℝ) (h : ∀ i, 0 < ρ i) :
    Lam ((Finset.range N).prod ρ) ((Finset.range N).sum φ)
      = (Finset.range N).sum (fun i => Lam (ρ i) (φ i)) := by
  induction N with
  | zero => simp [Lam]
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.sum_range_succ, Finset.sum_range_succ]
    rw [prenary_lam_add ((Finset.range n).prod ρ) (ρ n) ((Finset.range n).sum φ) (φ n)
        (Finset.prod_pos (fun i _ => h i)) (h n)]
    rw [ih]

end PrenaryDay28Q
