import Mathlib

/-! ================================================================
   偏元数学 · Day28-15 · 一般和乐 · N 步分离性
   ------------------------------------------------------------------
   核心：把两步/三步分离性推广到任意 N 步 ——
         ∏ᵢ (ρᵢ·e^{iφᵢ}) = (∏ᵢ ρᵢ) · e^{i·Σᵢ φᵢ}。
         归纳步正是两步分离性，故本件同时见证"分离性可迭代"这一结构。
   本稿范围：一引理 ＋ 两定理
     引理   prenary_hol_two       : 两步分离性（本件自带）
     定理1  prenary_hol_prod       : N 步分离性
     定理2  prenary_hol_prod_const : 纯旋转情形（各步模为 1）⟹ ∏λ = e^{i·Σφ}
   不做：不主张"一般和乐"具有物理意义；不引入 S¹ 的绕数（π₁）；
         不涉及"接入"；不主张闭路条件（Σφ ∈ 2πℤ）已形式化。
   注：本件自带所需引理（含两步分离性），独立可提交。
   日期：2026-09-27
   纪律：逐字提交 —— 抬头是提交原文的一部分，改动即改 SHA256。
   ================================================================ -/

namespace PrenaryDay28N

/-- 引理（两步分离性，本件自带）：两个动作复数之积 ＝ 模之积 · e^{i·角之和} -/
theorem prenary_hol_two (r s a b : ℝ) :
    (↑r * Complex.exp (↑a * Complex.I)) * (↑s * Complex.exp (↑b * Complex.I))
      = (↑(r * s)) * Complex.exp (↑(a + b) * Complex.I) := by
  have h : (↑(a + b) : ℂ) * Complex.I = ↑a * Complex.I + ↑b * Complex.I := by
    push_cast
    ring
  rw [h, Complex.exp_add]
  push_cast
  ring

/-- 定理1（N 步分离性）：∏ (ρᵢ·e^{iφᵢ}) = (∏ρᵢ)·e^{i·Σφᵢ} -/
theorem prenary_hol_prod (N : ℕ) (r a : ℕ → ℝ) :
    (Finset.range N).prod (fun i => (↑(r i) * Complex.exp (↑(a i) * Complex.I)))
      = (↑((Finset.range N).prod r)) * Complex.exp (↑((Finset.range N).sum a) * Complex.I) := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [Finset.prod_range_succ, Finset.prod_range_succ, Finset.sum_range_succ, ih,
        prenary_hol_two ((Finset.range n).prod r) (r n) ((Finset.range n).sum a) (a n)]

/-- 定理2（纯旋转情形的和乐）：各步模为 1 ⟹ ∏λ = e^{i·Σφ} -/
theorem prenary_hol_prod_const (N : ℕ) (a : ℕ → ℝ) :
    (Finset.range N).prod (fun i => (↑(1 : ℝ) * Complex.exp (↑(a i) * Complex.I)))
      = Complex.exp (↑((Finset.range N).sum a) * Complex.I) := by
  rw [prenary_hol_prod N (fun _ => (1 : ℝ)) a]
  simp

end PrenaryDay28N
