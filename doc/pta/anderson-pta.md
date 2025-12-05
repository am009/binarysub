
写一个field-sensitive的指针分析算法。基于语法的，而不是基于图的。

首先收集trivial的约束。包括收集所有的object。求解的过程中可能会出现object的field的发现，此时再为它增加对应的指针对象。
先随便找个指针分析的benchmark，然后手写出一个指针问题语言，然后尝试手动求解。


```
foreach y ∈ V do changed(y) = true;

while ∃y.changed(y) do
    collapse zero weight cycles with Tarjan's algorithm
    collapse non-zero weight cycles to offsetRange.
    foreach n ∈ V in (weak) topological order do
        if changed(n) then
            changed(n) = false;
            // process complex constraints involving *n
            foreach c ∈ C(n) do case c of
                *(n + k) ⊇ w:
                    foreach v ∈ Sol[n] do
                        x = v + k;
                        if x ≤ end(v) ∧ w → x ∉ E do
                            E ∪= w → x;
                            if Sol[w] ⊈ Sol[x] do
                                Sol[x] ∪= Sol[w]; changed(x) = true;
                w ⊇ *(n + k):
                    foreach v ∈ Sol[n] do
                        x = v + k;
                        if x ≤ end(v) ∧ x → w ∉ E do
                            E ∪= x → w;
                            if Sol[x] ⊈ Sol[w] do
                                Sol[w] ∪= Sol[x]; changed(w) = true;
                *(n + k) ⊇ {w}:
                    foreach v ∈ Sol[n] do
                        x = v + k;
                        if x ≤ end(v) ∧ w ∉ Sol[x] do
                            Sol[x] ∪= {w}; changed(x) = true;
                // process outgoing edges from n
                foreach n →k w ∈ E do
                    foreach v ∈ Sol[n] do
                        x = v + k;
                        if x ≤ end(v) do Sol[w] ∪= {x};
                        if Sol[w] changed then changed(w) = true;
```






```
G = < V, E >  // Constraint Graph  
V: a set of nodes in graph  
E: a set of edges in graph  
WorkList: a vector of nodes  

1 foreach o → p do                 // Address rule  
2     pts(p) = {o}  
3     pushIntoWorklist(p)  
4 while WorkList ≠ ∅ do  
5     p ← popFromWorklist()  
6     foreach o ∈ pts(p) do  
7         foreach q →(store) p do           // Store rule  
8             if q →(copy) o ∉ E then  
9                 E ← E ∪ {q →(copy) o}    // Add copy edge  
10                pushIntoWorklist(q)  
11        foreach p →(load) r do           // Load rule  
12            if o →(copy) r ∉ E then  
13                E ← E ∪ {o →(copy) r}    // Add copy edge  
14                pushIntoWorklist(o)  
15        foreach p →(copy) x ∈ E do       // Copy rule  
16            pts(x) ← pts(x) ∪ pts(p)  
17            if pts(x) changed then  
18                pushIntoWorklist(x)
```
