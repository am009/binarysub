# MLsub in pointer


参考retypd的思想，区分指针的load和store类型。指针会有两个类型变量，一个是存入的store，和取出的load。类似于函数。另外有一个store到load的直接的数据流。

MLsub会有个从store到load的flow edge。如果有变量存到store，会直接连到load，作为load的upper bound。如果有变量使用load，则反过来会连到store的变量。有一个lower bound。 

指针的处理：对于所有的指针，都生成一对state（类型变量），分别表示指针的store类型和load类型。指针自身也正常生成一个状态，然后分别用store和load边指向这两个状态。load和store边暂时不按照结构体field的方式处理，甚至考虑外部记录。

边包括：
- 函数的参数，返回值
- 结构体成员边
- 子类型边，数据流边

关键函数
- merge函数：沿着数据流上下传递约束边。
- biunify函数，递归传递相同的边的biunify。

关键操作：
- 当遇到数据流：增加flow edge，或者触发biunify。
- 当遇到内存分配：为新的object分配类型变量节点，然后才是有个指针节点。
- 当遇到了load指令：增加load边。
- 当遇到了store指令：增加store边。

