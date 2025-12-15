# Binary Subtyping Library (binsub)

这个库实现了一个带有级别(level)的简单子类型约束求解器，基于Simple sub算法的实现。主要用于类型推断和多态类型系统

编程规范：
- 使用C++时，不能使用RTTI和异常。有错误时使用头文件中的expected（类似std::expected）作为返回值
- 使用std::visit以及在visit的函数中使用constexpr的if判断的时候，必须要完整判断所有可能的类型，然后在最后的else抛出编译错误

类型推理算法：
- binarysub/binarysub-utils.h 包含了相关的工具类的定义，包括
  - expected，类似std::expected，
  - Error结构体，包含一个简单的string成员
- binarysub/binarysub-core.cpp  binarysub-core.h 核心类型推理部分 binarysub-core-cmp.h 实现了SimpleType的比较运算
- binarysub/binarysub.cpp binarysub.h 类型简化等代码
- binarysub/simplesub-test.cpp 运行测试用例，主函数

SimpleSub中使用的简单的类似ML的语言部分：
- binarysub/simplesub-parser.cpp simplesub-parser.h 定义和parser
- binarysub/simplesub-infer.cpp simplesub-infer.h 上面语言的访问语法树的类型推理

辅助文件：
- build.sh 编译和运行demo.cpp的脚本
- doc/二进制类型推理.md： 当前实现的算法的介绍
- doc/simplesub/simplesub-paper.md： simple sub的算法论文。文件非常长，仅在明确说明要读论文的时候读取，没有说明时不要读取这个文件

### 注意事项

尽量少用搜索去搜索代码，而是找到并直接读取整个代码文件
