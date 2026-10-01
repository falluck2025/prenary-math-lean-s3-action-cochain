[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23076134.svg)](https://doi.org/10.5281/zenodo.23076134)

# 偏元数学 · Day28 · 动作上链与和乐（F 的代数 · 保区间 · 望远镜 · 动作型 vs 拓扑型 · 非上边界 · 退化＝回收 · 判据之不足 · 缩放的两档 · 补量-乘法同构 · 两档互逆配对 · 归一化残差 · 一般和乐的分离性 · N 步分离 · 对数化 · 平移出界与乘性留内 · 相对尺度与三投影 · 方向侧 κ 同型 · 复缩放显式刻画）· Lean 4 形式化验证

## Prenary Mathematics · Day28 · Action Cochain and Holonomy (Algebra of F · Interval Preservation · Telescoping · Action-type vs Topological-type · Non-boundary · Degeneration as Recovery · Limits of the Criterion · Two Grades of Scaling · Complement Multiplicativity · Inverse Pairing · Normalized Residual · Separation of General Holonomy · N-step Separation · Logarithmisation · Translation Leaves ℂ★ while Multiplication Stays · Relative Scale and Three Projections · Direction-side κ Isomorphism · Explicit Characterisation of Complex Scaling) · Lean 4 Formal Verification

本文工作尚未得到独立实验验证，全部结论均为形式化验证层面的初步结果。

> **DOI**：DOI: 10.5281/zenodo.23076134。本仓库为偏元数学 S3（第三程）数学侧的**第三段**，上承 Day27 `prenary-math-lean-s3-residual-persistence`（残差为什么消不掉 · 层分离强化），并与 Day25 `prenary-math-lean-s3-sw-epsilon-eta`（ε↔η 映射）互为参照。

## 摘要

**问题**：既然 A1 规定「每次动作都留一个残差 `ε`」，那么——**这个残差究竟是"对象层的差"，还是"动作自己产生的东西"？**

**答**：把它落到一个**可算的对象**上（偏差 `c` 与和乐 `Hol`），再用**"是否正比于步数"**把动作型量与经典的上边界型量分开；随后**明确这条判据的界限**，并把**缩放（径向）**这一支的代数基本事实落定，最后把"两个分量"（角向 ⊕ 径向）的**一般和乐**与**偏好量**补全。

**一、残差层的不变区间（Day28-01／-02）**：残差落在开区间 `(0, δ₀)`。在其上定义保区间运算 `F(x,y;c) = x + y − xy/c`（等价于补量乘法 `c − F = (c−x)(c−y)/c`）：**基准固定时严格结合**；**基准随状态时，结合性差有精确公式** `a·d·(c₂−c₁)/(c₁c₂)`。`F` **把 `(0,c)` 映回 `(0,c)`**。

**二、判别工具（Day28-03）**：凡能写成"端点差"的量（**上边界型**），沿任何回到起点的路径，其和必为 `0`（**望远镜/伸缩求和**）。

**三、主结果（Day28-04／-05／-06）**：在纯旋转情形（`ε·cos δ = 0 ⟹ cos δ = 0`，故 `δ = π/2`）下走一圈：

| 量 | 值 | 行为 |
|:--|:--|:--|
| 位置标架角之和 `Σ Δψ` | `2π` | ⭐ **与步数 `N` 无关**（拓扑型） |
| 动作偏差之和 `Σ δ` | `N·(π/2)` | ⭐ **正比于 `N`**（动作型） |

⭐ 由两者**并置** ⟹ **动作量不能写成端点差 ⟹ `c` 不是上边界**。

**四、退化＝回收（Day28-07）**：⚠️ **退化（`ε → 0`）不是"和乐趋于 0"**（我们的是 `Hol ∝ 1/ε`，方向相反）。⭐ **正确的是"降阶/回收"**：设走一圈 `ε·N = L`，则 **`Hol·ε = (π/2)·L`**；⭐ 即**经典量在退化中被收回**。

**五、判据的界限（Day28-08）**：可见性**只到"残差层不含 `0`"这一步**——"非零"本身不足以区分（任意小的非零正实数存在）；⭐ 且"有标准上界"**不给**正下界，故**不能用"有没有上界"去区分非标准无穷小**。**真正的区分需要一个"手段"参数，属物理侧。**

**六、缩放的两档（Day28-09）**：缩放（`r ∈ ℝ_{>0}`）的"比例"与"二选一"是同一件事的两面——**`r ↦ 1/r` 是一个对合**，唯一不动点 `r = 1`（"不缩放"）；⭐ 并落定 **"缩放不改方向"**（正实数缩放保持辐角）。

**七、缩放那一支的代数（Day28-10／-11／-12）**：`F` 的补量形式是**乘性**的——在归一化补量 `φ(x) = (c−x)/c` 下，⭐ **`F` 就是普通乘法**（`φ(F) = φ(x)·φ(y)`）；取对数后，⭐ **`F` 就是加法**（这是"乘性 ↔ 加性"的桥）。缩放的两档（放大／缩小）在代数上是**互逆配对**（`r·s = 1 ∧ r>0 ⟹ (r<1 ↔ 1<s)`）；⭐ 而把取值限制在 `(0, δ₀)` 后，**倒数把有界区间送到无界区间**（`1/δ₀ < 1/r`）——这是"量的偏好（区间不对称）"的算术起点。⭐ 归一化残差 `x/c` 落在 `(0,1)`，且 **`φ(x) = 1 − x/c`**，即**补量与归一化残差互补为 1**——⭐ 「残差与上界的比值」这个量由此摆到明处。

**八、一般和乐：分离性与对数化（Day28-13／-15／-18）**：动作取复数形 `λ = ρ·e^{iφ}`（`ρ>0`），**一般和乐 ＝ 各步之积 `∏λₙ`**。⭐ **分离性**：`∏λₙ = (∏ρₙ)·e^{i·Σφₙ}`（两步 → 三步 → 任意 `N` 步，**归纳步正是两步分离性**）；⭐ **对数化**：`Λ(ρ,φ) := (log ρ, φ)` 是"**乘性合成 → 加法合成**"的同态（`Λ(∏ρ, Σφ) = Σ Λ(ρᵢ,φᵢ)`）。⚠️ **一个关键设计判断**：**不使用 `Complex.log`** —— 其主值会把角压回 `(−π, π]`、**抹掉"提升"**，与本框架的"非上边界性"直接冲突；改用**两个分量分别处理**（模用 `Real.log`，角直接用 ℝ 提升）。

**九、四类变化的对照（Day28-16）**：复数域上的"变化"分平移·旋转·缩放。⭐ **平移是加性的**——它可把 `ℂ★` 里的点送到 `0`（**出界**）；⭐ **旋转与缩放是乘性的**（`w·z`）——乘法**保持非零且可逆**，故是 `ℂ★` 上的**群运算**，而平移不是。⭐ 这解释了为何"残差层 `ε ∈ ℂ★`"与"平移"**不是同一类结构**。

**十、量的偏好：相对尺度与三投影（Day28-17／-19／-20）**：`§9` 的**偏好量**改用**相对尺度**（以区间 `(0,δ₀)` 为单位），得无量纲量 **`Pref(δ₀) = 1 − 2/δ₀`**；⭐ 它同时是「**测度投影**」（放大侧与缩小侧的**落侧差**）与「**统计投影**」（均匀分布下**一阶矩偏离不动点的 2 倍**）——⭐ **三投影在均匀下一致**；⭐ 且 `Pref = 0 ⟺ δ₀ = 2`（**不动点恰落在区间中点**）。⭐ **方向侧同型（K2）**：`κ = ⟨cos φ⟩` 与"偏离中点"**同形态**——对径配对相消（`cos φ + cos(φ+π) = 0`）、四方向 `κ = 0`（无偏好）、**缺一角 `κ = 1/3 ≠ 0`**（有偏好）。

**十一、复缩放的显式刻画（Day28-21／-22）**：把缩放因子写成极式 `λ = |λ|·e^{i·arg λ}`，则 ⭐ **复缩放 ＝ 实缩放（乘 `|λ|`）∘ 旋转（乘 `e^{i·arg λ}`）**；并落定**模律**（`‖λz‖ = ‖λ‖·‖z‖`）、**保 `ℂ★`**、**可结合**，以及**极式复原的桥引理**（`(‖w‖:ℂ)·exp(arg w·I) = w`，对全体 `ℂ` 成立）。

**不在范围内**：**不主张任何物理数值对应**；**不主张** `π₁(ℂ★) = ℤ` 已形式化（Mathlib 无现成件，改用实值 `ΣΔψ = 2π` 表达绕数）；**不写一般动作序列**（纯旋转情形）；**不主张"径向二态"已成立**（Day28-09 只给对合与两档划分的机器事实）；**不主张"量的偏好"已成立**（Day28-10／-11／-12／-17／-19 只给代数与算术事实）；**不主张 K1／K2 的"统一"已被证明**（只给两个实例的**形态一致**）；**不引入 `Complex.log`**；**不主张这三类变化穷尽一切**；**不给"接入"的运算规则**。

## Abstract

**Question**: Given A1 ("every action leaves a residual `ε`"), is this residual a **difference on the object layer**, or **something the action itself produces**?

**Answer**: reduce it to a **computable object** (the deviation `c` and the holonomy `Hol`), separate the action-type quantity from the classical boundary-type quantity by **whether it scales with the step count**, then **state the limits of that criterion**, fix the **algebraic basic facts about scaling (the radial part)**, and finally complete the **general holonomy** and the **preference quantity** (the two components: angular ⊕ radial).

**I. The invariant interval (Day28-01/-02)**: the residual lies in `(0, δ₀)`. On it, `F(x,y;c) = x + y − xy/c` (equivalent to `c − F = (c−x)(c−y)/c`): **strictly associative when the gauge is fixed**; **the associativity defect has an exact formula** `a·d·(c₂−c₁)/(c₁c₂)`. `F` **maps `(0,c)` into `(0,c)`**.

**II. The discriminating tool (Day28-03)**: any "endpoint difference" (**boundary-type**) sums to `0` along any closed path (**telescoping sum**).

**III. Main results (Day28-04/-05/-06)**: in pure rotation (`ε·cos δ = 0 ⟹ cos δ = 0`, so `δ = π/2`), one lap gives `Σ Δψ = 2π` (**independent of `N`**, topological type) and `Σ δ = N·(π/2)` (**proportional to `N`**, action type). ⭐ Juxtaposition ⟹ **`c` is not a boundary**.

**IV. Degeneration as recovery (Day28-07)**: ⚠️ degeneration (`ε → 0`) does **NOT** make the holonomy vanish (ours scales `Hol ∝ 1/ε`). ⭐ Correct statement: with `ε·N = L`, **`Hol·ε = (π/2)·L`** — ⭐ the classical quantity is **recovered**.

**V. Limits of the criterion (Day28-08)**: visibility stops at "the residual layer excludes `0`" — "nonzero" alone **cannot** distinguish (arbitrarily small nonzero positives exist); and a standard upper bound does **not** give a positive lower bound, so "having an upper bound" **fails** to separate nonstandard infinitesimals. **The real separation needs a "means" parameter and belongs to the physical side.**

**VI. Two grades of scaling (Day28-09)**: "ratio" and "two-way choice" are two faces of one thing — **`r ↦ 1/r` is an involution** with the unique fixed point `r = 1`; ⭐ and **"scaling does not change direction"** is fixed (positive scaling preserves the argument).

**VII. The algebra of the scaling branch (Day28-10/-11/-12)**: the complement form of `F` is **multiplicative** — under the normalised complement `φ(x) = (c−x)/c`, ⭐ **`F` is ordinary multiplication** (`φ(F) = φ(x)·φ(y)`); taking logarithms turns it into ⭐ **addition** (the multiplicative↔additive bridge). The two grades of scaling (magnify/shrink) are **inverse pairs** (`r·s = 1 ∧ r>0 ⟹ (r<1 ↔ 1<s)`); ⭐ restricting to `(0,δ₀)`, the reciprocal **sends the bounded interval to an unbounded one** (`1/δ₀ < 1/r`) — the arithmetic starting point of "a preference in magnitude (interval asymmetry)". ⭐ The normalised residual `x/c` lies in `(0,1)` and **`φ(x) = 1 − x/c`**: complement and normalised residual sum to 1 — ⭐ the "residual-to-bound ratio" is thereby brought into the open.

**VIII. General holonomy: separation and logarithmisation (Day28-13/-15/-18)**: an action takes the complex form `λ = ρ·e^{iφ}` (`ρ>0`); the **general holonomy is the product `∏λₙ`**. ⭐ **Separation**: `∏λₙ = (∏ρₙ)·e^{i·Σφₙ}` (two steps → three → arbitrary `N`; **the inductive step is exactly two-step separation**). ⭐ **Logarithmisation**: `Λ(ρ,φ) := (log ρ, φ)` is a homomorphism from **multiplicative composition to additive composition**. ⚠️ **A key design decision**: **`Complex.log` is NOT used** — its principal value folds the angle back into `(−π, π]` and **erases the lift**, clashing with this framework's "non-boundary property"; instead the **two components are handled separately** (`Real.log` for the modulus, plain ℝ for the angle).

**IX. The three kinds of change (Day28-16)**: over ℂ the changes are translation, rotation, scaling. ⭐ **Translation is additive** — it can send a point of `ℂ★` to `0` (**leaves ℂ★**); ⭐ **rotation and scaling are multiplicative** (`w·z`) — multiplication **preserves non-zeroness and is invertible**, hence a **group operation** on `ℂ★`, which translation is not. ⭐ This explains why "the residual layer `ε ∈ ℂ★`" and "translation" are **not the same kind of structure**.

**X. Preference in magnitude: relative scale and three projections (Day28-17/-19/-20)**: the **preference quantity** is recast in **relative scale** (in units of `(0,δ₀)`), giving the dimensionless **`Pref(δ₀) = 1 − 2/δ₀`**; ⭐ it is simultaneously the "**measure projection**" (the **side-difference** of the expand/shrink measures) and the "**statistical projection**" (twice the deviation of the mean from the fixed point, under uniformity) — ⭐ **the three projections agree under uniformity**; ⭐ and `Pref = 0 ⟺ δ₀ = 2` (the **fixed point sits exactly at the interval midpoint**). ⭐ **Direction-side isomorphism (K2)**: `κ = ⟨cos φ⟩` shares the **same form** as "deviation from the midpoint" — antipodal pairing cancels (`cos φ + cos(φ+π) = 0`), four directions give `κ = 0` (no preference), and **missing one corner gives `κ = 1/3 ≠ 0`** (preference).

**XI. Explicit characterisation of complex scaling (Day28-21/-22)**: writing the scaling factor in polar form `λ = |λ|·e^{i·arg λ}`, ⭐ **complex scaling ＝ real scaling (× `|λ|`) ∘ rotation (× `e^{i·arg λ}`)**; and the modulus law, preservation of `ℂ★`, associativity, and the **bridge lemma of polar reconstruction** (`(‖w‖:ℂ)·exp(arg w·I) = w`, for all `ℂ`) are fixed.

**Out of scope**: **no physical numerical correspondence**; no claim that `π₁(ℂ★) = ℤ` has been formalised; **no general action sequences**; **no claim that a "radial two-state" holds** (Day28-09 gives only involution and the two-grade split); **no claim that "a preference in magnitude" holds** (Day28-10/-11/-12/-17/-19 give algebraic and arithmetic facts only); **no claim that the K1/K2 "unification" has been proved** (only the **sameness of form** of two instances); **`Complex.log` is not introduced**; **no claim that these three kinds of change are exhaustive**; **no operational rule for "access"**.

## 关键词

偏元数学；动作残差；残差层；上边界；偏差上链；和乐；望远镜求和；动作型不变量；拓扑型不变量；保区间运算；结合性差；退化即回收；判据的界限；缩放的两档；倒数对合；补量-乘法同构；对数可加性；归一化残差；互逆配对；区间不对称；一般和乐；分离性；N 步分离；对数化；四类变化；平移出界；乘性留内；相对尺度；偏好量；三投影一致；方向侧同型；复缩放显式刻画；极式分拆；可证伪性；Lean 4；形式化验证；陈偏贞；老陈与AI的深夜实验室；PGI蛟龙；华夏思哲偏元注

## 概述

偏元数学是对经典数学的扩展尝试，`ε = 0` 时退化为经典。

本仓库回答一个**具体问题**：**残差是"对象层的差"，还是"动作自己产生的东西"？** 并把这条答案的**界限**与**另一半（缩放）**、以及**两个分量的一般和乐与偏好量**一并落定。

| 步骤 | 做的事 | 结论 |
|:--|:--|:--|
| 1 | 把残差放到**可算的对象**上（`c`、`Hol`） | `c` 依赖位置，`Hol` 是沿路径的累积 |
| 2 | 造一个**对照物**（上边界型） | 上边界量在闭路上**恒为 0** |
| 3 | **并置**两者 | 动作量闭路**不为 0** ⟹ **`c` 不是上边界** |
| 4 | **交代界限** | 可见性只到"不含 0"；真区分需"手段"参数（物理侧） |
| 5 | **另一支起步** | 缩放：`r ↦ 1/r` 对合 ＋ 不改方向 |
| 6 | **另一支的代数** | `φ` 下 `F`＝乘法，取 log＝加法；两档＝互逆配对；`x/c ∈ (0,1)` |
| 7 | **一般和乐** | `∏λₙ = (∏ρₙ)·e^{i·Σφₙ}`（分离性）；`Λ` 是乘法↔加法的同态 |
| 8 | **四类变化** | 平移是加性（出界），旋转/缩放是乘性（留内、可逆） |
| 9 | **量的偏好** | `Pref(δ₀) = 1 − 2/δ₀`；测度/统计/几何三投影在均匀下一致；方向侧 `κ` 同型 |
| 10 | **复缩放** | `λ = |λ|e^{i·arg λ}` ⟹ 复缩放 ＝ 实缩放 ∘ 旋转 |

> **后续**：本仓上承 Day27（残差为什么消不掉），并与 Day25（ε↔η 弱结构桥）互为参照。**发布文案不互相越读。**

## 核心定义

```lean
-- Day28-01/-02/-10：残差层不变区间上的保区间运算（等价于补量乘法）
noncomputable def F (x y c : ℝ) : ℝ := x + y - x*y/c

-- Day28-04：位置标架角的"走一圈"模型（先除后乘，使相邻差恒为 2π/N）
noncomputable def psi (N : ℕ) (i : ℕ) : ℝ := (2 * Real.pi / N) * i

-- Day28-04/-05：纯旋转情形下的动作偏差（由 K0 约束 cos δ = 0 给出）
noncomputable def delta : ℝ := Real.pi / 2

-- Day28-07：和乐（纯旋转情形）：每步留下 π/2，N 步累积
noncomputable def hol (N : ℕ) : ℝ := (N : ℝ) * (Real.pi / 2)

-- Day28-17/-19：偏好量（相对尺度）：Pref(δ₀) = 1 − 2/δ₀（无量纲）
noncomputable def Pref (δ₀ : ℝ) : ℝ := 1 - 2 / δ₀

-- Day28-18：对数化（乘性合成 → 加法合成）：Λ(ρ,φ) = (log ρ, φ)，值域 ℝ × ℝ
noncomputable def Lam (ρ φ : ℝ) : ℝ × ℝ := (Real.log ρ, φ)

-- Day28-21/-22：复缩放（乘一个非零复数；w 为缩放因子、z 为被作用的对象）
def cscale (w z : ℂ) : ℂ := w * z
```

## 定理清单

> **如实说明**：全部命题均为**结构性**的（不涉及数值物理），**不构成**关于"哪一层拥有 `ε`"的断言；Day28-08 的两条进一步**限定**了可见性判据的适用范围。并列陈述是为了让每一步可被单独检视，**读者若统计"定理数量"，应以"不同命题数"为准**。

### Day28-01 · F 的代数与结合性差（3 条）
| 定理 | 命题 |
|:--|:--|
| `F_assoc_defect` | 基准变化导致的非结合量有精确公式 `a·d·(c₂−c₁)/(c₁c₂)` |
| `F_assoc_same` | 基准相同时**严格结合** |
| `F_complement` | 补量形式：`c − F x y c = (c−x)(c−y)/c` |

### Day28-02 · 保区间与正性（5 条）
| 定理 | 命题 |
|:--|:--|
| `F_complement` | 补量形式（自带） |
| `F_pos` | `0<x, y<c` ⟹ `0 < F x y c` |
| `F_lt` | `x<c, y<c` ⟹ `F x y c < c` |
| `eps_ne_zero` | `0 < ε` ⟹ `ε ≠ 0` |
| `F_preserves_interval` | **`F` 把 `(0,c)` 映回 `(0,c)`** |

### Day28-03 · 望远镜（上边界量）（2 条）
| 定理 | 命题 |
|:--|:--|
| `boundary_telescope` | 上边界量沿有限路径之和 = 端点差 |
| `boundary_closed_zero` | **闭路 ⟹ 上边界量之和 = 0** |

### Day28-04 · 动作型 vs 拓扑型（4 条）
| 定理 | 命题 |
|:--|:--|
| `psi_step` | `ψ_N(i+1) − ψ_N(i) = 2π/N` |
| `sum_psi` | **`Σ Δψ = 2π`（与 `N` 无关）** |
| `sum_delta` | **`Σ δ = N·(π/2)`（∝ `N`）** |
| `contrast` | `N=4` 与 `N=8` 的动作量和**不等** |

### Day28-05 · 纯旋转角 `δ = π/2`（K0 约束）（4 条）
| 定理 | 命题 |
|:--|:--|
| `cos_eq_zero_of_mul` | `ε≠0 ∧ ε·cos δ = 0` ⟹ `cos δ = 0` |
| `cos_pi_div_two_zero` | `cos(π/2) = 0` |
| `spin_requires_cos_zero` | `0<ε ∧ ε·cos δ = 0` ⟹ `cos δ = 0` |
| `cos_pi_div_two_mem_Icc` | `π/2` 是 `[0,π]` 内的零点 |

### Day28-06 · 非上边界的算术核（4 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_telescope` | 望远镜引理（独立成定理） |
| `N_mul_pi_div_two_ne_zero` | `0<N` ⟹ `N·(π/2) ≠ 0` |
| `action_sum_nonzero` | **动作量和在闭路上 ≠ 0** |
| `action_not_boundary` | ⭐ **并置陈述 ⟹ `c` 不是上边界** |

### Day28-07 · 退化定理（回收式／降阶式）（4 条 ＋ 1 定义）
| 条 | 命题 |
|:--|:--|
| `hol`（定义） | 和乐 `Hol(N) = N·(π/2)` |
| `hol_mul_eps` | ⭐ **`ε·N = L ⟹ Hol·ε = (π/2)·L`**（回收式） |
| `hol_mul_eps_div` | 降阶式：再除 `δ₀` 仍成立 |
| `classical_vs_new` | 分量对照 |
| `hol_mono` | `N<M ⟹ Hol N < Hol M`（越精确越大） |

### Day28-08 · 判据之不足与缩放不改方向（4 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_small_nonzero` | ⭐ **任意小的非零正实数存在**（"非零"不足以区分） |
| `bounded_no_pos_lower` | ⭐ **有上界不给正下界**（上界不能区分非标准无穷小） |
| `scale_normSq` | 缩放只改模：`normSq((↑r)*z) = r²·normSq z` |
| `scale_preserves_arg` | ⭐ **缩放不改方向**：`arg((↑r)*z) = arg z`（`r>0`） |

### Day28-09 · 缩放的两档与倒数对合（4 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_inv_involutive` | ⭐ **`1/(1/r) = r`**（对合） |
| `prenary_inv_fixed_iff_one` | ⭐ **`0<r ⟹ (1/r = r ⟺ r = 1)`**（唯一不动点） |
| `prenary_trichotomy` | `r<1 ∨ r=1 ∨ 1<r`（两档＋分界） |
| `prenary_inv_lt_one_of_one_lt` | `1<r ⟹ 1/r < 1`（两侧互换） |

### Day28-10 · 补量-乘法同构与对数可加性（2 条 ＋ 1 定义）
| 条 | 命题 |
|:--|:--|
| `F`（定义） | 保区间运算（自带，同 Day28-01） |
| `F_complement_mul` | ⭐ **归一化补量下 `F` 就是乘法**：`(c−F)/c = ((c−x)/c)·((c−y)/c)` |
| `F_complement_log` | ⭐ **取对数后 `F` 就是加法**：`log((c−F)/c) = log((c−x)/c) + log((c−y)/c)` |

### Day28-11 · 互逆配对的两档与区间不对称（2 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_inv_pair_lt_one` | ⭐ **互逆配对**：`r·s = 1 ∧ 0<r ⟹ (r<1 ↔ 1<s)` |
| `prenary_inv_image_Ioo` | ⭐ **区间不对称**：`0<r<δ₀ ⟹ 1/δ₀ < 1/r`（倒数把有界区间送出界） |

### Day28-12 · 归一化残差与补量（3 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_phi_eq` | ⭐ **补量 ＝ 1 − 归一化残差**：`(c−x)/c = 1 − x/c` |
| `prenary_normalized_in_Ioo` | ⭐ **归一化残差落在 `(0,1)`**：`0<x<c ⟹ x/c ∈ (0,1)` |
| `prenary_phi_in_Ioo` | ⭐ **补量落在 `(0,1)`**：`0<x<c ⟹ φ(x) ∈ (0,1)` |

### Day28-13 · 一般和乐的分离性（3 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_hol_two` | ⭐ **两步分离性**：`(r·e^{ia})(s·e^{ib}) = (rs)·e^{i(a+b)}` |
| `prenary_hol_three` | **三步分离性**（由两步迭代两次，⭐ 见证"分离性可迭代"） |
| `prenary_hol_ne_zero` | `ρ>0 ⟹ λ ≠ 0`（对应残差层 `ε ∈ ℂ★`） |

### Day28-14 · 两档余量与 `δ₀ = 2`（3 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_small_side_full` | `δ₀ ≤ 1 ⟹ (0,δ₀)` 全在缩小侧（**没有"放大"档**） |
| `prenary_both_sides` | `1 < δ₀ ⟹ 两档皆非空` |
| `prenary_margin_balance` | ⭐ **两档余量相等 ⟺ `δ₀ = 2`**（缩小侧 `min δ₀ 1`、放大侧 `max (δ₀−1) 0`） |

### Day28-15 · 一般和乐的 N 步分离性（1 引理 ＋ 2 条）
| 条 | 命题 |
|:--|:--|
| `prenary_hol_two`（引理） | 两步分离性（本件自带） |
| `prenary_hol_prod` | ⭐ **N 步分离性**：`∏ᵢ(ρᵢ·e^{iφᵢ}) = (∏ᵢρᵢ)·e^{i·Σᵢφᵢ}` |
| `prenary_hol_prod_const` | 纯旋转情形（各步模为 1）⟹ `∏λ = e^{i·Σφ}` |

### Day28-16 · 平移出界与乘性留内（3 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_translation_leaves_star` | ⭐ **平移出界**：`a≠0 ⟹ ∃z≠0, z+a=0`（平移不保持 `ℂ★`） |
| `prenary_mul_stays_star` | ⭐ **乘性留内**：`w≠0 ∧ z≠0 ⟹ w·z ≠ 0` |
| `prenary_mul_invertible` | ⭐ **乘性可逆**：`w≠0 ⟹ ∃μ, μ·w = 1`（乘法是 `ℂ★` 上的群运算） |

### Day28-17 · 偏好量的相对尺度与对称性（K1）（1 定义 ＋ 4 条）
| 条 | 命题 |
|:--|:--|
| `Pref`（定义） | 偏好量 `Pref(δ₀) = 1 − 2/δ₀`（相对尺度，无量纲） |
| `prenary_pref_eq` | ⭐ **显式形式**：`Pref(δ₀) = 1 − 2/δ₀` |
| `prenary_pref_zero_iff` | ⭐ **两档等宽 ⟺ 不动点落在中点**：`Pref(δ₀) = 0 ⟺ δ₀ = 2` |
| `prenary_opposite_pair_zero` | 方向侧：对径成对相消 `cos x + cos(x+π) = 0` |
| `prenary_dir_moment_zero` | 方向侧：四个对称方向的 `cos` 之和 = 0 |

### Day28-18 · 一般和乐的对数化（A2）（1 定义 ＋ 3 条）
| 条 | 命题 |
|:--|:--|
| `Lam`（定义） | 对数化 `Λ(ρ,φ) = (log ρ, φ)`，值域 `ℝ × ℝ` |
| `prenary_lam_add` | ⭐ **单步同态**：`Λ(ρ₁ρ₂, φ₁+φ₂) = Λ(ρ₁,φ₁) + Λ(ρ₂,φ₂)` |
| `prenary_lam_three` | 三步（由定理 1 迭代） |
| `prenary_lam_sum` | ⭐ **N 步**：`Λ(∏ρ, Σφ) = Σ Λ(ρᵢ,φᵢ)` |

### Day28-19 · 偏好量：三投影在"均匀"下的一致（K1）（1 定义 ＋ 4 条）
| 条 | 命题 |
|:--|:--|
| `Pref`（定义） | 偏好量几何特值 `Pref(δ₀) = 1 − 2/δ₀`（数版） |
| `prenary_pref_offcenter` | 几何读法：`Pref = 2·(中点 − 不动点)` |
| `prenary_pref_measure_projection` | ⭐ **测度投影**：落侧差 `(1 − 1/δ₀) − 1/δ₀ = Pref` |
| `prenary_pref_stat_projection` | ⭐ **统计投影**：`⟨u⟩ = 1/2 ⟹ 2·(⟨u⟩ − 1/δ₀) = Pref` |
| `prenary_pref_balanced` | ⭐ **平衡**：`Pref = 0 ⟺ δ₀ = 2` |

### Day28-20 · 方向侧 κ 与量侧 Pref 的同型（K2）（3 条）
| 定理 | 命题 |
|:--|:--|
| `prenary_cos_pair` | ⭐ **对合配对**：`cos φ + cos(φ+π) = 0` |
| `prenary_kappa_uniform` | ⭐ **无偏好**：四方向（两对对径）⟹ `κ = 0` |
| `prenary_kappa_missing` | ⭐ **有偏好**：缺一角 ⟹ 三元平均 `κ = 1/3 ≠ 0` |

### Day28-21 · 复缩放的显式刻画（1 定义 ＋ 4 条）
| 条 | 命题 |
|:--|:--|
| `cscale`（定义） | 复缩放 `cscale w z = w·z` |
| `prenary_cscale_norm` | 模律：`‖λz‖ = ‖λ‖·‖z‖` |
| `prenary_cscale_ne_zero` | 保 `ℂ★`：非零乘非零仍非零 |
| `prenary_cscale_assoc` | 可结合：`cscale w (cscale v z) = cscale (w·v) z` |
| `prenary_cscale_polar` | ⭐ **极式分拆**：`cscale (r·e^{iθ}) z = r·(e^{iθ}·z)` |

### Day28-22 · 复缩放的 arg 桥 · 收口（1 定义 ＋ 2 条）
| 条 | 命题 |
|:--|:--|
| `cscale`（定义） | 复缩放 `cscale w z = w·z`（自带） |
| `prenary_norm_mul_exp_arg` | ⭐ **极式复原（桥）**：`(‖w‖:ℂ)·exp(arg w·I) = w` |
| `prenary_cscale_arg_form` | ⭐ **显式刻画**：`w·z = (‖w‖:ℂ)·exp(arg w·I)·z` ⟹ **复缩放 ＝ 实缩放 ∘ 旋转** |

## 验证记录

| 文件 | 内核 | Comparator | Challenge Hash（锁挑战） | 代码 SHA256（锁解答） |
|:--|:--|:--|:--|:--|
| Day28-01 | No goals + All Messages (0) | ✅ 通过 | `09d1c332fda3816f09ce3e279801c6ab54d084c23b5962177f884fdc180006ea` | 同左 |
| Day28-02 | No goals + All Messages (0) | ✅ 通过 | `19c989301b6b417d80130a8aafffb26bc5e9dfc0b223a29269c7f33eaa193919` | 同左 |
| Day28-03 | No goals + All Messages (0) | ✅ 通过 | `b0014c54f7201d5e137cb734e696fa3ee96bda7c977dbb6eabc02c237837710b` | 同左 |
| Day28-04 | No goals + All Messages (0) | ✅ 通过 | `4eb32795449ec3efe8496bf68c2239aa967920d1a344dba347bee49581bb5e66` | 同左 |
| Day28-05 | No goals + All Messages (0) | ✅ 通过 | `75e85c36d77dad285c65b3f653b4533715beb821678759f29a60356d8c732ca9` | 同左 |
| Day28-06 | No goals + All Messages (0) | ✅ 通过 | `6a866843206ea351fd902830de39b99eac18908e7c50b15283ab3051570b7185` | 同左 |
| Day28-07 | No goals + All Messages (0) | ✅ 通过 | `a138cbbaa32cee68789ad0715330fa86ec1b61e061c6b68d3edb24ba6b8965ef` | 同左 |
| Day28-08 | No goals + All Messages (0) | ✅ 通过 | `0322a2869f006b1e563d717edd283f5aefb519801de8cbe47ffc0e8e541a7959` | 同左 |
| Day28-09 | No goals + All Messages (0) | ✅ 通过 | `e31f5206ca13bca4f9f92428d0a8c5d36280c84680841141861e2e40dfb59f88` | 同左 |
| Day28-10 | No goals + All Messages (0) | ✅ 通过 | `b7d951f963f2db8983b54c73a74c161dbd63244c47365232758cc0a1cc51efa9` | 同左 |
| Day28-11 | No goals + All Messages (0) | ✅ 通过 | `3c101e2e897ad624866d58b11d6a047415f74816a9fd77f3203ed3b3d256e27c` | 同左 |
| Day28-12 | No goals + All Messages (0) | ✅ 通过 | `8db8e7279f750043278f9539f85bff0973b2e969dcb24ea021fd52644441b9f0` | 同左 |
| Day28-13 | No goals + All Messages (0) | ✅ 通过 | `334e6aa04a650e7ce066479ed21cfb51c7edb8203fb6ec64f48c10c5b6cafe7a` | 同左 |
| Day28-14 | No goals + All Messages (0) | ✅ 通过 | `69a1a65baf789950ae76dbe5e40b45558aac002c5408f6acf2598db6ca065c17` | 同左 |
| Day28-15 | No goals + All Messages (0) | ✅ 通过 | `99f0aaa1ab05c3088426cd78b63c38ba86fc535f9300607142a139ff5fe4313e` | 同左 |
| Day28-16 | No goals + All Messages (0) | ✅ 通过 | `e928af66992ba720e90a67c1d0142dfa8d2619e9870ece1ff0b056e0746c738d` | 同左 |
| Day28-17 | No goals + All Messages (0) | ✅ 通过 | `b54f59b4a54d364cda674b404d5630d72300deacdfe4369feb119072be1666c4` | 同左 |
| Day28-18 | No goals + All Messages (0) | ✅ 通过 | `75e7b2d967c6394f9f58fb6b95adde384a870afdc756a159dbe63ce9867eef7e` | 同左 |
| Day28-19 | No goals + All Messages (0) | ✅ 通过 | `c4a23bdf0ac12ab1ee24339e44b415eb3396fade3cd298ccee927bfd33142ff0` | 同左 |
| Day28-20 | No goals + All Messages (0) | ✅ 通过 | `1e2229553b1baf3e36a191bcbb589e7cbcc86f61dcc198bb89675f15b4a6d871` | 同左 |
| Day28-21 | No goals + All Messages (0) | ✅ 通过 | `e7071df4f3172964915d139d09d2b5f6eda9dc1e60aea1e7d84591f477094cfc` | 同左 |
| Day28-22 | No goals + All Messages (0) | ✅ 通过 | `92c5bfa5034cd2084c413e5ade63615add96c2da7ad8f90afa846699a7b0c842` | 同左 |

- **平台**：L∃∀N Comparator Live (Experimental) · Latest Mathlib
- **验证时间**：2026-09-27 ～ 2026-09-29
- **双哈希说明**：本组采用**自编 challenge** 模式（Challenge 文本 ＝ 我方提交代码），故 **Challenge Hash 与代码 SHA256 取同一值**（界面原文："You have previously committed to trust that this challenge is free of errors or misleading content (SHA256 …)"）；已用本地 `sha256sum` 与界面显示值**逐字核对一致**。
- ⚠️ **改稿记录**：Day28-01（补 `noncomputable`）、-02（`_hx`/`_hy` 清 linter）、-03（弃 `∑` 记法改 `Finset.sum`）、-04（`push_cast` 后 `ring`；删多余 `ring`）、-05（定理 4 降级为"零点在 `[0,π]` 内"）、-06（望远镜独立成定理）、-08（第二稿：改用 `Complex.normSq` 与 `Complex.arg_real_mul`）、-09（定理 4 三次调整，终稿改为纯 `nlinarith`）、-12（`field_simp` 已自行关闭目标，删多余 `ring`）、-15（弃 `∑ i in s` 记法，改用 `Finset.range` 的 `.prod`/`.sum`）、-17／-19（`Pref` 须标 `noncomputable`，定义体含除法）、-18（**不用 `Complex.log`**；`Lam` 须标 `noncomputable`；收尾用 `congrArg` 硬接）、-21（首跑连踩两雷：抬头 `/-` 触发嵌套注释、形参名 `λ` 是 `fun` 关键字 ⟹ 改名 `w`）、-22（桥引理用 Mathlib 自带 `Complex.norm_mul_exp_arg_mul_I`）。**表中 22 个哈希均为终稿 SHA256，且已逐件与落盘文件 `sha256sum` 核对一致。**

## 文件说明

```
.
├── Day28-01_F的代数与结合性差_LEAN源码_20260927.lean          # 3 条
├── Day28-02_保区间与正性_LEAN源码_20260927.lean               # 5 条
├── Day28-03_望远镜上边界_LEAN源码_20260927.lean               # 2 条
├── Day28-04_动作型与拓扑型_LEAN源码_20260927.lean             # 4 条
├── Day28-05_纯旋转角pi2_LEAN源码_20260927.lean                # 4 条
├── Day28-06_非上边界算术核_LEAN源码_20260927.lean             # 4 条
├── Day28-07_退化定理_LEAN源码_20260927.lean                   # 4 条 ＋ 1 定义（★ 回收式）
├── Day28-08_判据之不足与缩放不改方向_LEAN源码_20260927.lean    # 4 条
├── Day28-09_缩放的两档与倒数对合_LEAN源码_20260927.lean        # 4 条
├── Day28-10_补量乘法同构与对数可加性_LEAN源码_20260927.lean    # 2 条 ＋ 1 定义
├── Day28-11_互逆配对的两档与区间不对称_LEAN源码_20260927.lean  # 2 条
├── Day28-12_归一化残差与补量_LEAN源码_20260927.lean           # 3 条
├── Day28-13_一般和乐的分离性_LEAN源码_20260927.lean           # 3 条
├── Day28-14_两档余量与δ0等于2_LEAN源码_20260927.lean          # 3 条
├── Day28-15_一般和乐的N步分离性_LEAN源码_20260927.lean        # 1 引理 ＋ 2 条
├── Day28-16_平移出界与乘性留内_LEAN源码_20260927.lean         # 3 条
├── Day28-17_偏好量的相对尺度与对称性_LEAN源码_20260928.lean    # 1 定义 ＋ 4 条
├── Day28-18_一般和乐的对数化A2_LEAN源码_20260928.lean         # 1 定义 ＋ 3 条
├── Day28-19_偏好量三投影的一致_LEAN源码_20260929.lean         # 1 定义 ＋ 4 条
├── Day28-20_方向侧kappa与量侧Pref的同型_LEAN源码_20260929.lean # 3 条
├── Day28-21_复缩放的显式刻画_LEAN源码_20260929.lean           # 1 定义 ＋ 4 条
├── Day28-22_复缩放的arg桥_LEAN源码_20260929.lean              # 1 定义 ＋ 2 条
├── README.md
├── LICENSE
└── evidence/                                                  # 验证截图（内核 / Comparator）
```

**合计：22 个 `.lean` · 定理 72 条 ＋ 引理 1 条 ＋ 5 类定义（`F`／`hol`／`Pref`／`Lam`／`cscale`，部分定义在件间重复出现）。**

## 复现方式

1. 打开 `https://comparator.live.lean-lang.org/`（Latest Mathlib）。
2. 将对应 `.lean` 文件**整份复制**（Ctrl+A，含 `import Mathlib` 与 `/-!` 抬头），分别贴入 **Challenge** 与 **Candidate Solution** 面板。
3. 运行内核，确认 `All Messages = 0`；再点二次验证，应显示 `Trusting challenge with hash <SHA256>` 且结果为通过。
4. 用 `sha256sum <file>.lean` 计算哈希，与上表**逐字核对**。

## 可证伪条件

1. 若存在 `0<x,y<c` 使 `F x y c ∉ (0,c)` ⟹ `F_preserves_interval` 失效；
2. 若基准相同时 `F` 不结合 ⟹ `F_assoc_same` 失效；
3. 若存在闭路使上边界量之和不等于 `0` ⟹ `boundary_closed_zero` 失效；
4. 若纯旋转下 `ε·cos δ = 0` 允许 `cos δ ≠ 0` ⟹ `spin_requires_cos_zero` 失效；
5. 若存在 `N ≥ 1` 使动作量之和为 `0` ⟹ `c` 非上边界的论证失效；
6. 若 `ε·N = L` 时 `Hol·ε ≠ (π/2)·L` ⟹ 退化回收式失效；
7. 若存在**非零但不可任意小**的实数列（即在 `(0,δ₀)` 内取值有正下界）⟹ `bounded_no_pos_lower` 所刻画的"上界不给下界"失效；
8. 若存在正实数 `r` 使 `arg(r·z) ≠ arg z` ⟹ `scale_preserves_arg` 失效；
9. 若存在正实数 `r ≠ 1` 使 `1/r = r` ⟹ `prenary_inv_fixed_iff_one` 失效；
10. 若存在 `c ≠ 0` 与 `x` 使 `(c−x)/c ≠ 1 − x/c` ⟹ `prenary_phi_eq` 失效；
11. 若存在 `r·s = 1, r>0` 使 `r<1` 与 `1<s` 不等价 ⟹ `prenary_inv_pair_lt_one` 失效；
12. 若存在某 `N` 步与 `ρ,φ` 使 `∏(ρᵢ·e^{iφᵢ}) ≠ (∏ρᵢ)·e^{i·Σφᵢ}` ⟹ `prenary_hol_prod`（分离性）失效；
13. 若存在 `0<δ₀` 使 `min δ₀ 1 = max (δ₀−1) 0` 但 `δ₀ ≠ 2` ⟹ `prenary_margin_balance` 失效；
14. 若存在 `N` 步与 `ρᵢ>0` 使 `Λ(∏ρ, Σφ) ≠ Σ Λ(ρᵢ,φᵢ)` ⟹ `prenary_lam_sum`（对数化同态）失效；
15. 若存在非零复数 `w,z` 使 `w·z = 0`，或存在非零平移不能把某点送出 `ℂ★` ⟹ 相关条失效；
16. 若存在 `0<δ₀` 使三投影在均匀下不一致（如 `Pref ≠` 落侧差） ⟹ `prenary_pref_measure_projection`／`prenary_pref_stat_projection` 失效；
17. 若存在 `φ` 使 `cos φ + cos(φ+π) ≠ 0` ⟹ `prenary_cos_pair`（方向侧对合配对）失效；
18. 若存在正 `r` 与 `θ` 使复缩放不等于"实缩放 ∘ 旋转" ⟹ `prenary_cscale_polar`／`prenary_cscale_arg_form` 失效；
19. 若存在复数 `w` 使 `(‖w‖:ℂ)·exp(arg w·I) ≠ w` ⟹ `prenary_norm_mul_exp_arg`（极式复原桥）失效；
20. 若本仓任何一条在 Lean 4（Mathlib）中重跑**不通过** ⟹ 相应条目的形式化主张失效。

## 引用与许可

- 作者：**陈松（Chen Song）**｜ORCID：`0009-0002-9510-2239`
- GitHub：`github.com/falluck2025`
- License：**CC BY-NC-ND 4.0**

## 作者致谢

感谢一切偶然的必然和必然的偶然。

本文及相关仓库的作者为**民科独立研究者**，全部工作自 2026 年 2 月 14 日起**为爱发电**进行中。若您认同本研究的方向，并有意为这份独立工作提供任何支持，欢迎通过以下邮箱与作者联系：**pgi_cs_cbs@163.com**。我们都将在后续论文预印本的"致谢"中如实记录，以志不忘。

## 作者备注（非正文）

- **本仓与 S-006 的关系**：本仓对应 **NEW(S)-006《方向的回归》** 的**核心构造与主结果部分**（偏差 `c`、和乐 `Hol`、非上边界、退化＝回收、一般和乐与两个分量、量的偏好、复缩放显式刻画），以及 V1.1／V1.2 的自我限定（可见性判据的界限）。⚠️ **本仓为形式化落点；论文与仓库互为支撑，但发布文案不互相越读。**
- **层级声明**：`F` 的选取是**选择**（由同胚参数化）；纯旋转（`δ = π/2`）是 **K0 约束下的特例**，一般动作序列**留待后续**；Day28-09 的"缩放两档"**只是对合与三分**，**"它构成一个二态"是推演，不在本仓**；Day28-10／-11／-12／-17／-19 给出的是**代数与算术事实**，**"量的偏好（区间不对称）因此成立"是推演，不在本仓**；Day28-17／-19／-20 的"三投影一致""方向侧同型"是**两个实例的形态一致**，**"K1／K2 的统一已被证明"是推演，不在本仓**。
- **诚实边界**：Day28-06 的"非上边界"在机器侧落为**"闭路和 ≠ 0"与"上边界闭路恒 0"的并置**，**不是"不存在任何 `f`"的全称证明**；Day28-05 定理 4 只给"零点位于 `[0,π]` 内"，**唯一性未形式化**；Day28-08 只证"**非零不足以区分**"，**不证**"动作残差与经典误差项不能区分"（那需要"手段"参数，属物理侧）；Day28-12 的 `x/c ∈ (0,1)` 是**归一化位置**，**不主张**它与物理侧任何量成比例；Day28-18 的 `Λ` **不使用 `Complex.log`**（主值会抹掉"提升"），"角"的连续提升**未形式化**（提升是"沿序列"的性质）；Day28-19 的"均匀"以 `⟨u⟩ = 1/2` 这一条假设代替（**不假装连续**）。
- **纪律**：抬头不含 DOI／版本等会随发布变动的字段（改则动哈希）。逐字提交。
- ⚠️ **关于抬头中的排障备注（本仓的选择）**：Day28-01～-06 的抬头保留了撰写阶段的备注（"⚠️ 跑之前：本件未在本地编译过……若报错请贴回"）。⭐ 这些文字是**提交原文的一部分**（改一字即改 SHA256）；经权衡，本仓**选择保留原样**，以维持"提交文本 ＝ 落盘文件 ＝ 发布文件"三处同一份。⭐ **它们的实际状态以本文件"验证记录"为准：全部 22 件均已通过内核与 Comparator 双重验证。**
- **证据链**：Lean 内核 `No goals` ＋ Comparator 双哈希 ＋ Git 时间戳 ＋ Zenodo DOI ＋ `evidence/` 截图。

---

**老陈与AI的深夜实验室 发布 请笑纳**
