# CoOccurrence Analysis in TypeSimplifier

## 概述

CoOccurrence分析是TypeSimplifier.scala中实现的一种类型简化技术，用于识别和合并在类型系统中总是一起出现的类型变量。该分析基于这样的观察：如果两个类型变量在相同的极性位置总是一起出现，那么它们在语义上是等价的，可以被统一。

## 核心思想

### 基本原理

如果类型变量`'a`总是在正极性（resp. 负极性）位置与某个`'b`一起出现，且反过来也成立，那么这两个变量是无法区分的，因此可以被统一。

### 重要注意事项

**易错点**：算法检查的是在**给定极性下**，一个变量是否总是与另一个变量共现。只需要在**一个极性**下满足共现条件就可以进行统一，不需要在两个极性下都共现。

例如在`'a -> 'b -> 'a | 'b`中：
- 负极性：'a和'b分别单独出现（在不同的参数位置）
- 正极性：'a和'b总是一起出现（在并集中）
- **关键**：由于在正极性下它们总是共现，算法可以将它们统一

这种统一是**语义安全的**，因为：
1. **约束等价性**：在正极性下共现的变量会收到相同的上界约束
2. **子类型关系保持**：统一后不会创造或破坏子类型关系
3. **可居住性保持**：类型的可居住性不会改变

**示例**：
- `('a & 'b) -> ('a, 'b)` 等同于 `'a -> ('a, 'a)`
- `'a -> 'b -> 'a | 'b` 等同于 `'a -> 'a -> 'a`

**不能统一的反例**：
- `('a & 'b) -> 'b -> ('a, 'b)` **不**等同于 `'a -> 'a -> ('a, 'a)`
- 因为需要 `'a :> b | a & b <: a & b`，这不是有效的约束

### 扩展思想

移除那些总是与某个具体类型在正负极性位置都一起出现的变量：
- 例如：`'a ∧ Int -> 'a ∨ Int` 等同于 `Int -> Int`
- 这来自约束 `'a :> Int <: 'b` 和 `'b <: Int`（基本上说 `'a =:= 'b =:= Int`）

## 数据结构

### 核心数据结构（TypeSimplifier.scala:190-193）

```scala
val coOccurrences: MutMap[(Boolean, Variable), MutSet[SimpleType]] = LinkedHashMap.empty
val varSubst = MutMap.empty[Variable, Option[Variable]]
```

- **coOccurrences**: 映射每个极性变量（极性+变量）到与其共现的类型集合
  - `Boolean`表示极性：`true`为正位置，`false`为负位置
  - `MutSet[SimpleType]`存储共现的类型（变量和原始类型）

- **varSubst**: 记录变量替换/统一
  - `Some(var)` 表示与另一个变量统一
  - `None` 表示消除该变量

## 算法实现

### 分析阶段（TypeSimplifier.scala:196-227）

`go`函数遍历类型结构并执行以下操作：

#### 1. 记录共现关系（197-203行）
```scala
ty.vars.foreach { tv =>
  allVars += tv
  val newOccs = LinkedHashSet.from(ty.vars.iterator ++ ty.prims)
  coOccurrences.get(pol -> tv) match {
    case Some(os) => os.filterInPlace(newOccs) // 计算交集
    case None => coOccurrences(pol -> tv) = newOccs
  }
}
```

- 对于紧凑类型中的每个变量`tv`，记录所有一起出现的变量和原始类型
- 使用交集保持只有一致共现的类型

#### 2. 处理递归变量（204-212行）
```scala
cty.recVars.get(tv).foreach { b => // 如果`tv`是递归的，也处理其界`b`
  if (!recVars.contains(tv)) {
    lazy val goLater: () => CompactType = {
      recVars += tv -> (() => goLater())
      go(b, pol)
    }; goLater
  }; ()
}
```

- 处理递归变量的界
- 使用惰性求值避免无限递归

### 优化策略

#### 1. 单极性变量消除（232-239行）

```scala
(coOccurrences.get(true -> v0), coOccurrences.get(false -> v0)) match {
  case (Some(_), None) | (None, Some(_)) =>
    varSubst += v0 -> None; ()
```

**原理**：只在正极性或负极性位置出现的变量不会有意义地约束类型系统，可以被消除。

#### 2. 变量统一（240-278行）

两个变量可以被统一，如果：
- 它们在相同极性中总是共现
- 它们有相同的递归状态（都是递归或都是非递归）

**算法步骤**：
1. 对每个变量`v`和极性`pol`
2. 检查每个共现变量`w`
3. 如果`w`在给定极性中总是与`v`共现，将`w`统一到`v`中
4. 适当地合并它们的界

**关键代码**：
```scala
if (coOccurrences.get(pol -> w).forall(_(v))) {
  println(s"[U] $w := $v") // 将w统一到v中
  varSubst += w -> Some(v)
  // 处理界的合并...
}
```

#### 3. 变量-原始类型统一（273-274行）

```scala
case atom: Primitive if (coOccurrences.get(!pol -> v).exists(_(atom))) =>
  varSubst += v -> None; ()
```

如果一个变量在两个极性中都与某个原始类型共现，则可以将该变量消除。

**示例**：`'a ∧ Int -> 'a ∨ Int` → `Int -> Int`

## 实现细节

### 伪循环检测

算法检测并移除不表示实际递归类型的人工循环：

```scala
if (parents(tv)) ct() // 我们有一个伪循环：忽略该界
```

### 规范化类型构造

`canonicalizeType`函数确保共现的递归类型被正确合并，使用类似幂集的构造：

```scala
def canonicalizeType(ty: SimpleType): CompactTypeScheme
```

这个过程类似于将NFA转换为DFA的幂集构造，原则上可能导致指数级更大的类型，但在实践中通常产生良好的简化。

### 哈希一致化

`coalesceCompactType`执行哈希一致化以创建更紧密的递归类型结：

```scala
def coalesceCompactType(cty: CompactTypeScheme): Type
```

## 复杂度考虑

1. **空间复杂度**：共现分析的空间复杂度主要由共现集合的大小决定
2. **时间复杂度**：分析阶段是线性的，但规范化可能导致指数级增长
3. **实践效果**：尽管理论上可能很复杂，但算法在实践中通常产生良好的简化

## 具体示例

### 示例1：基本变量统一
```
输入：('a & 'b) -> ('a, 'b)
分析：'a和'b在正极性中总是一起出现
输出：'a -> ('a, 'a)
```

### 示例2：变量-原始类型统一
```
输入：'a ∧ Int -> 'a ∨ Int
分析：'a在正负极性中都与Int共现
输出：Int -> Int
```

### 示例3：单极性变量消除
```
输入：'a -> Int（'a只在负极性出现）
分析：'a是单极性变量
输出：Bot -> Int（简化为Top）
```

## 调试输出

实现包含详细的调试输出：
- `[occ]`：显示共现关系
- `[rec]`：显示递归变量
- `[U]`：显示变量统一
- `[sub]`：显示最终替换映射

这些输出有助于理解算法的工作过程和调试类型简化问题。

## 结论

CoOccurrence分析是一种强大的类型简化技术，通过识别和利用类型变量之间的共现模式，能够显著简化复杂的类型表达式。该技术在保持类型系统语义正确性的同时，提供了有效的类型优化策略。