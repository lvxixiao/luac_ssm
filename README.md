### luac\_ssm

lua c 共享字符串, 基于lua 5.4.6, 不同版本的lua代码需要修改的源码可能不太一样, 只能做参考。

### 编译测试

    sh runtest.sh

### 思路

因为我是游戏服务器开发人员，所以实现上会以游戏服务器的实际场景出发，在游戏服务器中 只有最开始运行时的字符串是有必要共享的, 当程序启动后, 就会有玩家行为(如聊天)产生大量字符串, 这些字符串很少会有复用的机会, 所以可以简单的指定需要全局共享的字符串数量, 因此就不需要考虑字符串的回收问题, 实现起来可以简单粗暴。

##### 工作流程

ssm(share string map)使用散列表,预先分配好大量的队列,然后针对slot加读写锁。

在创建vm之前, main函数中初始化ssm的散列表, 以及指定全局字符串的数量。

1.  每次试图创建新的短字符串时候, 首先检查字符串在当前lua vm是否存在, 若已存在则返回。
2.  其次检查是否存在于ssm中, 若存在则返回
3.  检查ssm是否到达限制, 如果没有到达则加入这个新字符串并返回。否则加入当前lua vm的池中。

##### 需要注意

lua vm启动时, 会有一些短字符串创建并加入到 fixedgc 链表中, 意味着这个字符串不受 gc 控制，但是在lua vm推出时会free该内存。

因此我们需要避免ssm中的字符串被加入到 fixedgc 链表, 因此我在 TString 结构中加了一个 isglobal 标志, 当检测到这个标志时则不加入 fixedgc 链表。还有另一种方案是 GCobject的 tt 字段的 4-5 位用来标志类型, 在已经有长串跟短串类型的基础下, 再加一个类型, 但是这个方案会修改比较多的代码, 所以我没有选择。

### 参考文章

[共享lua vm间的小字符串](https://blog.codingnow.com/2015/08/lua_vm_share_string.html)
