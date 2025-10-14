# Binary Subtyping Library (binsub)

这个库实现了一个带有级别(level)的简单子类型约束求解器，基于MLsub算法的实现。主要用于类型推断和多态类型系统。

## 核心数据结构

### SimpleType 类型系统
- `SimpleType`: 使用 `std::shared_ptr<TypeNode>` 表示的类型
- `TypeNode`: 包含四种类型变体的联合体：
  - `TPrimitive`: 基本类型（如 int, bool）
  - `TVariable`: 类型变量，带有约束边界
  - `TFunction`: 函数类型 (参数类型 -> 返回类型)
  - `TRecord`: 记录类型，包含字段名和类型的有序对

### 级别管理
- `VarSupply`: 提供唯一的类型变量ID
- `Scope`: 管理嵌套作用域的级别
- `VariableState`: 存储类型变量的状态，包括上下界和级别信息

## 主要函数说明

### 类型创建函数
```cpp
// 创建基本类型
SimpleType make_primitive(std::string name);

// 创建类型变量
SimpleType make_variable(std::uint32_t id, int lvl);
SimpleType fresh_variable(VarSupply &vs, int lvl);

// 创建函数类型
SimpleType make_function(SimpleType a, SimpleType b);

// 创建记录类型
SimpleType make_record(std::vector<std::pair<std::string, SimpleType>> fields);
```

### 类型检查和访问
```cpp
// TypeNode 成员函数，用于类型判断
bool isTPrimitive() const;
bool isVariableState() const;
bool isTFunction() const;
bool isTRecord() const;

// 获取特定类型的指针（可能为nullptr）
TPrimitive* getAsTPrimitive();
TVariable* getAsVariableState();
TFunction* getAsTFunction();
TRecord* getAsTRecord();
```

### 约束求解
```cpp
// 主要的子类型约束函数
expected<void, Error> constrain(const SimpleType &lhs, const SimpleType &rhs, 
                               Cache &cache, VarSupply &supply);
```
实现子类型关系 `lhs <: rhs`，支持：
- 基本类型的相等性检查
- 函数类型的逆变/协变规则
- 记录类型的结构子类型
- 类型变量的约束传播

### 级别系统 (Extrusion)
```cpp
SimpleType extrude(const SimpleType &ty, bool pol, int lvl,
                   std::map<PolarVS, std::shared_ptr<VariableState>> &cache,
                   VarSupply &supply);
```
实现类型的"挤出"操作，用于处理不同级别之间的类型变量约束。

### 多态类型方案
```cpp
// 类型方案：单态和多态
using TypeScheme = std::variant<MonoScheme, PolyScheme>;

// 泛化：let多态中的类型泛化
TypeScheme generalize(const SimpleType &rhs, int env_level);

// 实例化：使用类型方案创建具体类型实例
SimpleType instantiate(const TypeScheme &sch, int at_level, VarSupply &supply);
```

### 工具函数
```cpp
// 计算类型中包含的最大级别
int level_of(const SimpleType &st);
```

## 使用示例

```cpp
#include "binsub.h"
using namespace binarysub;

int main() {
    VarSupply supply;
    Scope env;
    Cache cache;
    
    // 创建基本类型
    auto int_type = make_primitive("int");
    auto bool_type = make_primitive("bool");
    
    // 创建身份函数类型 α -> α
    env.enter();
    auto alpha = fresh_variable(supply, env.level);
    auto id_type = make_function(alpha, alpha);
    env.leave();
    
    // 泛化为多态类型方案
    auto id_scheme = generalize(id_type, 0);
    
    // 实例化使用
    auto id1 = instantiate(id_scheme, env.level, supply);
    auto id2 = instantiate(id_scheme, env.level, supply);
    
    // 约束求解：模拟函数应用
    auto& func1 = id1->getAsTFunctionRef();
    if (auto result = constrain(int_type, func1.lhs, cache, supply)) {
        // 约束成功
    }
    
    return 0;
}
```

## 错误处理

库使用自定义的 `expected<T, Error>` 类型进行错误处理，类似于 `std::expected`：
- 成功时包含值
- 失败时包含错误信息
- 提供 `has_value()`, `value()`, `error()` 等方法

## 特性

1. **级别约束系统**: 防止类型变量逃逸其定义作用域
2. **双向约束传播**: 类型变量同时维护上界和下界
3. **记录类型**: 支持结构化数据的子类型关系
4. **Let多态**: 支持类型泛化和实例化
5. **缓存优化**: 避免重复的约束求解