(** * Poly: 多态与高阶函数 *)

(* 最后提醒：请勿将习题解答放在可以公开访问的地方，谢谢！ *)

(* Suppress some annoying warnings from Coq: *)
Set Warnings "-notation-overridden,-parsing".
From LF Require Export Lists.

(* ################################################################# *)
(** * 多态 *)

(** 在本章中，我们会继续发展函数式编程的基本概念，其中最关键的新概念就是
    _'多态'_（在所处理的数据类型上抽象出函数）和_'高阶函数'_（函数作为数据）。 *)

(* ================================================================= *)
(** ** 多态列表 *)

(** 在上一章中，我们使用了只包含数的列表。很明显，
    有趣的程序还需要能够处理其它元素类型的列表，如字符串列表、布尔值列表、
    列表的列表等等。我们_'可以'_分别为它们定义新的归纳数据类型，例如... *)

Inductive boollist : Type :=
  | bool_nil
  | bool_cons (b : bool) (l : boollist).

(** ...不过这样很快就会变得乏味。
    部分原因在于我们必须为每种数据类型都定义不同的构造子，
    然而主因还是我们必须为每种数据类型再重新定义一遍所有的列表处理函数
    （ [length]、[rev] 等）以及它们所有的性质（[rev_length]、[app_assoc] 等）。 *)

(** 为避免这些重复，Coq 支持定义_'多态'_归纳类型。
    例如，以下就是_'多态列表'_数据类型。 *)

Inductive list (X:Type) : Type :=
  | nil
  | cons (x : X) (l : list X).

(** 这和上一章中 [natlist] 的定义基本一样，只是将 [cons] 构造子的
    [nat] 参数换成了任意的类型 [X]，函数头的第一行添加了 [X] 的绑定，
    而构造子类型中的 [natlist] 则换成了 [list X]。（我们可以重用构造子名
    [nil] 和 [cons]，因为之前定义的 [natlist] 在当前作用之外的一个 [Module] 中。）

    [list] 本身又是什么类型？一种不错的思路就是把 [list] 当做从 [Type]
    类型到 [Inductive] 归纳定义的_'函数'_；或者换种更简明的思路，即 [list]
    是个从 [Type] 类型到 [Type] 类型的函数。对于任何特定的类型 [X]，
    类型 [list X] 是一个 [Inductive] 归纳定义的，元素类型为 [X] 的列表的集合。 *)

Check list : Type -> Type.

(** [list] 的定义中的参数 [X] 自动
    成为构造子 [nil] 和 [cons] 的参数 —— 也就是说，[nil] 和 [cons] 在这里是多态
    的构造子；现在我们调用它们的时候必须要提供一个参数，就是它们要构造的列表的具
    体类型。例如，[nil nat] 构造的是 [nat] 类型的空列表。 *)

Check (nil nat) : list nat.

(** [cons nat] 与此类似，它将类型为 [nat] 的元素添加到类型为
    [list nat] 的列表中。以下示例构造了一个只包含自然数 3 的列表： *)

Check (cons nat 3 (nil nat)) : list nat.

(** [nil] 的类型会是什么呢？也许我们可以（根据定义）说它是 [list X]，
    不过这样它就不是接受 [X] 返回 [list] 的函数了。再提出一种：[Type -> list X]
    并没有解释 [X] 是什么，[(X : Type) -> list X] 则比较接近。
    Coq 对这种情况的记法为 [forall X : Type, list X]： *)

Check nil : forall X : Type, list X.

(** 类似地，定义中 [cons] 的类型看起来像 [X -> list X -> list X]
    然而以上述约定来解释 [X] 的含义则可以得到类型
    [forall X, X -> list X -> list X]。 *)

Check cons : forall X : Type, X -> list X -> list X.

(** （关于记法的附注：在 [.v] 文件中，量词“forall”会写成字母的形式，
    而在生成的 HTML 和一些设置了显示控制的 IDE 中，[forall]
    通常会渲染成一般的“倒 A”数学符号，虽然你偶尔还是会看到英文拼写的
    “forall”。这只是排版上的效果，它们的含义没有任何区别。） *)

(** 如果在每次使用列表构造子时，都要为它提供类型参数，那样会很麻烦。
    不过我们很快就会看到如何省去这种麻烦。 *)

Check (cons nat 2 (cons nat 1 (nil nat)))
      : list nat.

(** 现在我们可以回过头来定义之前写下的列表处理函数的多态版本了。
    例如 [repeat]：*)

Fixpoint repeat (X : Type) (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil X
  | S count' => cons X x (repeat X x count')
  end.

(** 同 [nil] 与 [cons] 一样，我们可以通过将 [repeat]
    应用到一个类型、一个该类型的元素以及一个数字来使用它： *)

Example test_repeat1 :
  repeat nat 4 2 = cons nat 4 (cons nat 4 (nil nat)).
Proof. reflexivity. Qed.

(** 要用 [repeat] 构造其它种类的列表，
    我们只需通过对应类型的参数将它实例化即可： *)

Example test_repeat2 :
  repeat bool false 1 = cons bool false (nil bool).
Proof. reflexivity. Qed.


(** **** 练习：2 星, standard (mumble_grumble) 

    考虑以下两个归纳定义的类型： *)

Module MumbleGrumble.

Inductive mumble : Type :=
  | a
  | b (x : mumble) (y : nat)
  | c.

Inductive grumble (X:Type) : Type :=
  | d (m : mumble)
  | e (x : X).

(** 对于某个类型 [X]，以下哪些是 [grumble X] 良定义的元素？
    （在各选项后填“是”或“否”。）
      - [d (b a 5)] 否
      - [d mumble (b a 5)] 是
      - [d bool (b a 5)] 是
      - [e bool true] 是
      - [e mumble (b c 0)] 是
      - [e bool (b c 0)] 否
      - [c] 否 *) 
(* 请在此处解答 *)
End MumbleGrumble.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_mumble_grumble : option (nat*string) := None.
(** [] *)

(* ----------------------------------------------------------------- *)
(** *** 类型标注的推断 *)

(** 我们再写一遍 [repeat] 的定义，不过这次不指定任何参数的类型。
    Coq 还会接受它么？ *)

Fixpoint repeat' X x count : list X :=
  match count with
  | 0        => nil X
  | S count' => cons X x (repeat' X x count')
  end.

(** 确实会。我们来看看 Coq 赋予了 [repeat'] 什么类型： *)

Check repeat'
  : forall X : Type, X -> nat -> list X.
Check repeat
  : forall X : Type, X -> nat -> list X.

(** 它与 [repeat] 的类型完全一致。Coq 可以使用_'类型推断'_
    基于它们的使用方式来推出 [X]、[x] 和 [count] 一定是什么类型。例如，
    由于 [X] 是作为 [cons] 的参数使用的，因此它必定是个 [Type] 类型，
    因为 [cons] 期望一个 [Type] 作为其第一个参数，而用 [0] 和 [S] 来匹配
    [count] 意味着它必须是个 [nat]，诸如此类。

    这种强大的功能意味着我们不必总是在任何地方都显式地写出类型标注，
    不过显式的类型标注对于文档和完整性检查来说仍然非常有用，
    因此我们仍会继续使用它。在代码中使用类型标注时，你应当把握好一个度，
    太多会导致混乱并分散注意力，太少则会迫使读者为理解你的代码而在大脑中进行类型推断。 *)

(* ----------------------------------------------------------------- *)
(** *** 类型参数的推断 *)

(** 要使用多态函数，我们需要为其参数再额外传入一个或更多类型。
    例如，前面 [repeat] 函数体中的递归调用必须传递类型 [X]。不过由于
    [repeat] 的第二个参数为 [X] 类型的元素，第一个参数明显只能是 [X]，
    既然如此，我们何必显式地写出它呢？

    幸运的是，Coq 允许我们避免这种冗余。在任何我们可以写类型参数的地方，我们都可
    以将类型参数写为 “洞” [_]，可以看做是说 “请 Coq 自行找出这里应该填什么。”
    更确切地说，当 Coq 遇到 [_] 时，它会尝试_'统一'_所有的局部变量信息，
    包括函数应当应用到的类型，其它参数的类型，以及应用函数的上下文中期望的类型，
    以此来确定 [_] 处应当填入的具体类型。

    这听起来很像类型标注推断。实际上，这两种个过程依赖于同样的底层机制。
    除了简单地忽略函数中某些参数的类型：

      repeat' X x count : list X :=

    我们还可以将类型换成洞：

      repeat' (X : _) (x : _) (count : _) : list X :=

    以此来告诉 Coq 要尝试推断出缺少的信息。

    Using holes, the [repeat] function can be written like this: *)

Fixpoint repeat'' X x count : list X :=
  match count with
  | 0        => nil _
  | S count' => cons _ x (repeat'' _ x count')
  end.

(** 在此例中，我们写出 [_] 并没有省略多少 [X]。然而在很多情况下，
    这对减少击键次数和提高可读性还是很有效的。例如，假设我们要写下一个包含数字
    [1]、[2] 和 [3] 的列表，此时不必写成这样： *)

Definition list123 :=
  cons nat 1 (cons nat 2 (cons nat 3 (nil nat))).

(** ……我们可以用洞来这样写： *)

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).

(* ----------------------------------------------------------------- *)
(** *** 隐式参数 *)

(** 我们甚至可以通过告诉 Coq _'总是'_推断给定函数的类型参数来在大多数情况下
    直接避免写 [_]。

    [Arguments] 用于指令指定函数或构造子的名字并列出其参数名，
    花括号中的任何参数都会被视作隐式参数。（如果定义中的某个参数没有名字，
    那么它可以用通配模式 [_] 来标记。这种情况常见于构造子中。） *)

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments repeat {X} x count.

(** 现在我们完全不用提供类型参数了： *)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(** 此外，我们还可以在定义函数时就声明隐式参数，
    只需要将某个参数两边的圆括号换成花括号。例如： *)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0        => nil
  | S count' => cons x (repeat''' x count')
  end.

(** （注意我们现在甚至不必在 [repeat'''] 的递归调用中提供类型参数了，
      实际上提供了反而是无效的，因为 Coq 并不想要它。）

    我们会尽可能使用最后一种风格，不过还会继续在 [Inductive] 构造子中使用显式的
    [Argument] 声明。原因在于如果将归纳类型的形参标为隐式的话，
    不仅构造子的类型会变成隐式的，类型本身也会变成隐式的。例如，
    考虑以下 [list] 类型的另一种定义： *)

Inductive list' {X:Type} : Type :=
  | nil'
  | cons' (x : X) (l : list').

(** 由于 [X] 在包括 [list'] 本身的_'整个'_归纳定义中都是隐式声明的，
    因此当我们讨论数值、布尔值或其它任何类型的列表时，都只能写 [list']，
    而写不了 [list' nat]、[list' bool] 等等，这样就有点过分了。 *)

(** 作为本节的收尾，我们为新的多态列表重新实现几个其它的标准列表函数... *)

Fixpoint app {X : Type} (l1 l2 : list X)
             : (list X) :=
  match l1 with
  | nil      => l2
  | cons h t => cons h (app t l2)
  end.

Fixpoint rev {X:Type} (l:list X) : list X :=
  match l with
  | nil      => nil
  | cons h t => app (rev t) (cons h nil)
  end.

Fixpoint length {X : Type} (l : list X) : nat :=
  match l with
  | nil => 0
  | cons _ l' => S (length l')
  end.

Example test_rev1 :
  rev (cons 1 (cons 2 nil)) = (cons 2 (cons 1 nil)).
Proof. reflexivity. Qed.

Example test_rev2:
  rev (cons true nil) = cons true nil.
Proof. reflexivity. Qed.

Example test_length1: length (cons 1 (cons 2 (cons 3 nil))) = 3.
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** 显式提供类型参数 *)

(** 用 [Implicit] 将参数声明为隐式的会有个小问题：Coq
    偶尔会没有足够的局部信息来确定类型参数。此时，我们需要告诉 Coq
    这次我们会显示地给出参数。例如，假设我们写了如下定义： *)

Fail Definition mynil := nil.

(** （[Definition] 前面的 [Fail] 限定符可用于_'任何'_指令，
    它的作用是确保该指令在执行时确实会失败。如果该指令失败了，Coq
    就会打印出相应的错误信息，不过之后会继续处理文件中剩下的部分。）

    在这里，Coq 给出了一条错误信息，因为它不知道应该为 [nil] 提供何种类型。
    我们可以为它提供个显式的类型声明来帮助它，这样 Coq 在“应用”[nil]
    时就有更多可用的信息了： *)

Definition mynil : list nat := nil.

(** 此外，我们还可以在函数名前加上前缀 [@] 来强制将隐式参数变成显式的： *)

Check @nil : forall X : Type, list X.

Definition mynil' := @nil nat.

(** 使用参数推断和隐式参数，我们可以为列表定义和前面一样的简便记法。
    由于我们让构造子的的类型参数变成了隐式的，因此 Coq
    就知道在我们使用该记法时自动推断它们了。 *)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

(** 现在列表就能写成我们希望的方式了： *)

Definition list123''' := [1; 2; 3].

(* ----------------------------------------------------------------- *)
(** *** 练习 *)

(** **** 练习：2 星, standard, optional (poly_exercises) 

    下面是一些简单的练习，和 [Lists] 一章中的一样。
    为了实践多态，请完成下面的证明。 *)

Theorem app_nil_r : forall (X:Type), forall l:list X,
  l ++ [] = l.
Proof.
  intros X l. induction l as [| h t].
  - reflexivity.
  - simpl. rewrite -> IHt. reflexivity.
Qed. 

Theorem app_assoc : forall A (l m n:list A),
  l ++ m ++ n = (l ++ m) ++ n.
Proof.
  intros A l m n. induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.  

Lemma app_length : forall (X:Type) (l1 l2 : list X),
  length (l1 ++ l2) = length l1 + length l2.
Proof.
  intros X l1 l2. induction l1 as [| h t IHl].
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed. 
(** [] *)

(** **** 练习：2 星, standard, optional (more_poly_exercises) 

    这儿有些更有趣的东西... *)

Theorem rev_app_distr: forall X (l1 l2 : list X),
  rev (l1 ++ l2) = rev l2 ++ rev l1.
Proof.
  intros X l1 l2. induction l1 as [| h t IHl].
  - simpl. rewrite -> app_nil_r. reflexivity.
  - simpl. rewrite -> IHl. rewrite <- app_assoc. reflexivity.
Qed.  

Theorem rev_involutive : forall X : Type, forall l : list X,
  rev (rev l) = l.
Proof.
  intros X l. induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite -> rev_app_distr. simpl. rewrite -> IHl. reflexivity.
Qed. 
(** [] *)

(* ================================================================= *)
(** ** 多态序对 *)

(** 按照相同的模式，我们在上一章中给出的数值序对的定义可被推广为
    _'多态序对（Polymorphic Pairs）'_，它通常叫做_'积（Products）'_： *)

Inductive prod (X Y : Type) : Type :=
| pair (x : X) (y : Y).

Arguments pair {X} {Y} _ _.

(** 和列表一样，我们也可以将类型参数定义成隐式的，
    并以此定义类似的具体记法： *)

Notation "( x , y )" := (pair x y).

(** 我们也可以使用 [Notation] 来定义标准的_'积类型（Product Types）'_记法： *)

Notation "X * Y" := (prod X Y) : type_scope.

(** （标注 [: type_scope] 会告诉 Coq 该缩写只能在解析类型而非表达式时使用。
      这避免了与乘法符号的冲突。) *)

(** 一开始会很容易混淆 [(x,y)] 和 [X*Y]。不过要记住 [(x,y)]
    是一个_'值'_，它由两个其它的值构造得来；而 [X*Y] 是一个_'类型'_，
    它由两个其它的类型构造得来。如果 [x] 的类型为 [X] 而 [y] 的类型为 [Y]，
    那么 [(x,y)] 的类型就是 [X*Y]。 *)

(** 第一元（first）和第二元（second）的射影函数（Projection Functions）
    现在看起来和其它函数式编程语言中的很像了： *)

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with
  | (x, y) => x
  end.

Definition snd {X Y : Type} (p : X * Y) : Y :=
  match p with
  | (x, y) => y
  end.

(** 以下函数接受两个列表，并将它们结合成一个序对的列表。
    在其它函数式语言中，它通常被称作 [zip]。我们为了与 Coq 的标准库保持一致，
    将它命名为 [combine]。*)

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y)
           : list (X*Y) :=
  match lx, ly with
  | [], _ => []
  | _, [] => []
  | x :: tx, y :: ty => (x, y) :: (combine tx ty)
  end.
(** **** 练习：1 星, standard, optional (combine_checks) 

    请尝试在纸上回答以下问题并在 Coq 中检验你的解答：
    - [combine] 的类型是什么？（即 [Check @combine] 会打印出什么？）
    - 以下指令会打印出什么？
  
    forall X Y : Type, list X -> list Y -> list (X * Y)
  
    Compute (combine [1;2] [false;false;true;true]).

    [(1, false);(2, false)] : list (nat * bool)
*)
(** [] *)

(** **** 练习：2 星, standard, recommended (split) 

    函数 [split] 是 [combine] 的右逆（right inverse）：
    它接受一个序对的列表并返回一个列表的序对。
    在很多函数式语言中，它被称作 [unzip]。

    请在下面完成 [split] 的定义，确保它能够通过给定的单元测试。 *)

Fixpoint split {X Y : Type} (l : list (X*Y))
               : (list X) * (list Y)
  := match l with
     | [] => ([], [])
     | (x, y) :: t => (x :: fst (split t), y:: snd (split t))
     end.  

Example test_split:
  split [(1,false);(2,false)] = ([1;2],[false;false]).
Proof.
  reflexivity.
Qed.
(** [] *)

(* ================================================================= *)
(** ** 多态候选 *)

(** 最后一种要介绍的多态类型是_'多态候选（Polymorphic Options）'_,
    它推广了上一章中的 [natoption]（由于我们之后要用标准库中定义的
    [option] 版本，因此这里的定义我们把它放在模块中）： *)

Module OptionPlayground.

Inductive option (X:Type) : Type :=
  | Some (x : X)
  | None.

Arguments Some {X} _.
Arguments None {X}.

End OptionPlayground.

(** 现在我们可以重写 [nth_error] 函数来让它适用于任何类型的列表了。 *)

Fixpoint nth_error {X : Type} (l : list X) (n : nat)
                   : option X :=
  match l with
  | [] => None
  | a :: l' => if n =? O then Some a else nth_error l' (pred n)
  end.

Example test_nth_error1 : nth_error [4;5;6;7] 0 = Some 4.
Proof. reflexivity. Qed.
Example test_nth_error2 : nth_error [[1];[2]] 1 = Some [2].
Proof. reflexivity. Qed.
Example test_nth_error3 : nth_error [true] 2 = None.
Proof. reflexivity. Qed.

(** **** 练习：1 星, standard, optional (hd_error_poly) 

    请完成上一章中 [hd_error] 的多态定义，确保它能通过下方的单元测试。 *)

Definition hd_error {X : Type} (l : list X) : option X
  := match l with
     | [] => None
     | h :: t => Some(h)
     end.

(** 再说一遍，要强制将隐式参数转为显式参数，我们可以在函数名前使用 [@]。 *)

Check @hd_error : forall X : Type, list X -> option X.

Example test_hd_error1 : hd_error [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_error2 : hd_error  [[1];[2]]  = Some [1].
Proof. reflexivity. Qed.
(** [] *)

(* ################################################################# *)
(** * 函数作为数据 *)

(** 和大部分现代编程语言一样，特别是“函数式”的语言，包括 OCaml、Haskell、
    Racket、Scala、Clojure 等，Coq 也将函数视作“一等公民（First-Class Citizens）”，
    即允许将它们作为参数传入其它函数、作为结果返回、以及存储在数据结构中等等。 *)

(* ================================================================= *)
(** ** 高阶函数 *)

(** 用于操作其它函数的函数通常叫做_'高阶函数'_。以下是简单的示例： *)

Definition doit3times {X:Type} (f:X->X) (n:X) : X :=
  f (f (f n)).

(** 这里的参数 [f] 本身也是个（从 [X] 到 [X] 的）函数，
    [doit3times] 的函数体将 [f] 对某个值 [n] 应用三次。 *)

Check @doit3times : forall X : Type, (X -> X) -> X -> X.

Example test_doit3times: doit3times minustwo 9 = 3.
Proof. reflexivity. Qed.

Example test_doit3times': doit3times negb true = false.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 过滤器 *)

(** 下面是个更有用的高阶函数，它接受一个元素类型为 [X] 的列表和一个
    [X] 的谓词（即一个从 [X] 到 [bool] 的函数），然后“过滤”此列表并返回一个新列表，
    其中仅包含对该谓词返回 [true] 的元素。 *)

Fixpoint filter {X:Type} (test: X->bool) (l:list X)
                : (list X) :=
  match l with
  | []     => []
  | h :: t => if test h then h :: (filter test t)
                        else       filter test t
  end.

(** 例如，如果我们将 [filter] 应用到谓词 [evenb] 和一个数值列表 [l]
    上，那么它就会返回一个只包含 [l] 中偶数的列表。 *)

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X : Type} (l : list X) : bool :=
  (length l) =? 1.

Example test_filter2:
    filter length_is_1
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(** 我们可以使用 [filter] 给出 [Lists] 中 [countoddmembers]
    函数的简洁的版本。 *)

Definition countoddmembers' (l:list nat) : nat :=
  length (filter oddb l).

Example test_countoddmembers'1:   countoddmembers' [1;0;3;1;4;5] = 4.
Proof. reflexivity. Qed.
Example test_countoddmembers'2:   countoddmembers' [0;2;4] = 0.
Proof. reflexivity. Qed.
Example test_countoddmembers'3:   countoddmembers' nil = 0.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** ** 匿名函数 *)

(** 在上面这个例子中，我们不得不定义一个名为 [length_is_1] 的函数，
    以便让它能够作为参数传入到 [filter] 中，由于该函数可能再也用不到了，
    这有点令人沮丧。我们经常需要传入“一次性”的函数作为参数，之后不会再用，
    而为每个函数取名是十分无聊的。

    幸运的是，有一种更好的方法。我们可以按需随时构造函数而不必在顶层中声明它
    或给它取名。 *)

Example test_anon_fun':
  doit3times (fun n => n * n) 2 = 256.
Proof. reflexivity. Qed.

(** 表达式 [(fun n => n * n)] 可读作“一个给定 [n] 并返回 [n * n] 的函数。” *)

(** 以下为使用匿名函数重写的 [filter] 示例：*)

Example test_filter2':
    filter (fun l => (length l) =? 1)
           [ [1; 2]; [3]; [4]; [5;6;7]; []; [8] ]
  = [ [3]; [4]; [8] ].
Proof. reflexivity. Qed.

(** **** 练习：2 星, standard (filter_even_gt7) 

    使用 [filter]（而非 [Fixpoint]）来编写 Coq 函数 [filter_even_gt7]，
    它接受一个自然数列表作为输入，返回一个只包含大于 [7] 的偶数的列表。 *)

Definition filter_even_gt7 (l : list nat) : list nat
  := filter (fun n => (evenb n) && (7 <? n)) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.

Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.
(** [] *)

(** **** 练习：3 星, standard (partition) 

    使用 [filter] 编写一个 Coq 函数 [partition]：

      partition : forall X : Type,
                  (X -> bool) -> list X -> list X * list X

   给定一个集合 [X]、一个类型为 [X -> bool] 的断言和一个 [list X]，
   [partition] 应当返回一个列表的序对。该序对的第一个成员为包含原始列表中
   满足该测试的子列表，而第二个成员为包含不满足该测试的元素的子列表。
   两个子列表中元素的顺序应当与它们在原始列表中的顺序相同。 *)

Definition partition {X : Type}
                     (test : X -> bool)
                     (l : list X)
                   : list X * list X
  :=  (filter test l, filter (fun x => negb (test x)) l). 

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.
(** [] *)

(* ================================================================= *)
(** ** 映射 *)

(** 另一个方便的高阶函数叫做 [map]。 *)

Fixpoint map {X Y: Type} (f:X->Y) (l:list X) : (list Y) :=
  match l with
  | []     => []
  | h :: t => (f h) :: (map f t)
  end.

(** 它接受一个函数 [f] 和一个列表 [ l = [n1, n2, n3, ...] ]
    并返回列表 [ [f n1, f n2, f n3,...] ]，其中 [f] 可分别应用于 [l]
    中的每一个元素。例如： *)

Example test_map1: map (fun x => plus 3 x) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

(** 输入列表和输出列表的元素类型不必相同，因为 [map] 会接受_'两个'_类型参数
    [X] 和 [Y]，因此它可以应用到一个数值的列表和一个从数值到布尔值的函数，
    并产生一个布尔值列表： *)

Example test_map2:
  map oddb [2;1;2;5] = [false;true;false;true].
Proof. reflexivity. Qed.

(** 它甚至可以应用到一个数值的列表和一个从数值到布尔值列表的函数，
    并产生一个布尔值的_'列表的列表'_： *)

Example test_map3:
    map (fun n => [evenb n;oddb n]) [2;1;2;5]
  = [[true;false];[false;true];[true;false];[false;true]].
Proof. reflexivity. Qed.

(* ----------------------------------------------------------------- *)
(** *** 习题 *)

(** **** 练习：3 星, standard (map_rev) 

    请证明 [map] 和 [rev] 可交换。你可能需要定义一个辅助引理 *)
Lemma map_comm : forall (X Y : Type) (f : X -> Y) (l1 l2: list X),
  map f (l1 ++ l2)= map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [| h t IHl].
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.  

Theorem map_rev : forall (X Y : Type) (f : X -> Y) (l : list X),
  map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| h t IHl].
  - simpl. reflexivity.
  - simpl. rewrite <- IHl. rewrite -> map_comm. simpl. reflexivity.
Qed. 
(** [] *)

(** **** 练习：2 星, standard, recommended (flat_map) 

    函数 [map] 通过一个类型为 [X -> Y] 的函数将 [list X] 映射到 [list Y]。
    我们可以定义一个类似的函数 [flat_map]，它通过一个类型为 [X -> list Y]
    的函数 [f] 将 [list X] 映射到 [list Y]。你的定义应当可以“压扁”[f]
    的结果，就像这样：

        flat_map (fun n => [n;n+1;n+2]) [1;5;10]
      = [1; 2; 3; 5; 6; 7; 10; 11; 12].
*)

Fixpoint flat_map {X Y: Type} (f: X -> list Y) (l: list X)
                   : (list Y)
  := match l with
     | [] => []
     | h :: t => f h ++ flat_map f t
     end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.
(** [] *)

(** [map] 这个函数不止对列表有意义，以下是一个在 [option] 上的 [map]：*)

Definition option_map {X Y : Type} (f : X -> Y) (xo : option X)
                      : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

(** **** 练习：2 星, standard, optional (implicit_args) 

    [filter] 和 [map] 的定义和应用在很多地方使用了隐式参数。
    请将隐式参数外层的花括号替换为圆括号，然后在必要的地方补充显式类型形参并用
    Coq 检查你做的是否正确。（本练习并不会打分，你可以在本文件的_'副本'_中做它，
    之后丢掉即可。）
*)
(** [] *)

(* ================================================================= *)
(** ** 折叠 *)

(** 一个更加强大的高阶函数叫做 [fold]。本函数启发自“[reduce] 归约”
    操作，它是 Google 的 map/reduce 分布式编程框架的核心。 *)

Fixpoint fold {X Y: Type} (f: X->Y->Y) (l: list X) (b: Y)
                         : Y :=
  match l with
  | nil => b
  | h :: t => f h (fold f t b)
  end.

(** 直观上来说，[fold] 操作的行为就是将给定的二元操作符 [f]
    插入到给定列表的每一对元素之间。例如，[ fold plus [1;2;3;4] ]
    直观上的意思是 [1+2+3+4]。为了让它更精确，我们还需要一个“起始元素”
    作为 [f] 初始的第二个输入。因此，例如

       fold plus [1;2;3;4] 0

    就会产生

       1 + (2 + (3 + (4 + 0))).

    以下是更多例子： *)

Check (fold andb) : list bool -> bool -> bool.

Example fold_example1 :
  fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 :
  fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 :
  fold app  [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

(** **** 练习：1 星, advanced (fold_types_different) 

    我们观察到 [fold] 由 [X] 和 [Y] 这_'两个'_类型变量参数化，形参 [f]
    则是个接受 [X] 和 [Y] 并返回 [Y] 的二元操作符。你能想出一种 [X] 和
    [Y] 不同时的应用情景吗？ *)
Example fold_example4 :
  fold cons [1;2;3;4] [5;6] = [1;2;3;4;5;6].
Proof. reflexivity. Qed.

(* 请在此处解答 *)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_fold_types_different : option (nat*string) := None.
(** [] *)

(* ================================================================= *)
(** ** 用函数构造函数 *)

(** 目前我们讨论过的大部分高阶函数都是接受函数作为参数的。
    现在我们来看一些将函数作为其它函数的结果_'返回'_的例子。
    首先，下面是一个接受值 [x]（由某个类型 [X] 刻画）并返回一个从
    [nat] 到 [X] 的函数，当它被调用时总是产生 [x] 并忽略其 [nat] 参数。 *)

Definition constfun {X: Type} (x: X) : nat->X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.

Example constfun_example1 : ftrue 0 = true.
Proof. reflexivity. Qed.

Example constfun_example2 : (constfun 5) 99 = 5.
Proof. reflexivity. Qed.

(** 实际上，我们已经见过的多参函数也是讲函数作为数据传入的例子。
    为了理解为什么，请回想 [plus] 的类型。 *)

Check plus : nat -> nat -> nat.

(** 该表达式中的每个 [->] 实际上都是一个类型上的_'二元'_操作符。
    该操作符是_'右结合'_的，因此 [plus] 的类型其实是 [nat -> (nat -> nat)]
    的简写，即，它可以读作“[plus] 是一个单参数函数，它接受一个 [nat]
    并返回另一个函数，该函数接受另一个 [nat] 并返回一个 [nat]”。
    在上面的例子中，我们总是将 [plus] 一次同时应用到两个参数上。
    不过如果我们喜欢，也可以一次只提供一个参数，这叫做_'偏应用（Partial
    Application）'_。 *)

Definition plus3 := plus 3.
Check plus3 : nat -> nat.

Example test_plus3 :    plus3 4 = 7.
Proof. reflexivity. Qed.
Example test_plus3' :   doit3times plus3 0 = 9.
Proof. reflexivity. Qed.
Example test_plus3'' :  doit3times (plus 3) 0 = 9.
Proof. reflexivity. Qed.

(* ################################################################# *)
(** * 附加练习 *)

Module Exercises.

(** **** 练习：2 星, standard (fold_length) 

    列表的很多通用函数都可以通过 [fold] 来实现。例如，下面是
    [length] 的另一种实现： *)

Definition fold_length {X : Type} (l : list X) : nat :=
  fold (fun _ n => S n) l 0.

Example test_fold_length1 : fold_length [4;7;0] = 3.
Proof. reflexivity. Qed.

(** 请证明 [fold_length] 的正确性。
    （提示：知道 [reflexivity] 的化简力度比 [simpl]
    更大或许会有所帮助。也就是说，你或许会遇到 [simpl] 无法解决但 [reflexivity]
    可以解决的目标。） *)

Theorem fold_length_correct : forall X (l : list X),
  fold_length l = length l.
Proof.
 intros X l. induction l as [| h t IHl].
 - simpl. reflexivity.
 - simpl. rewrite <- IHl. reflexivity.
Qed.  
(** [] *)

(** **** 练习：3 星, standard (fold_map) 

    我们也可以用 [fold] 来定义 [map]。请完成下面的 [fold_map]。 *)

Definition fold_map {X Y: Type} (f: X -> Y) (l: list X) : list Y
  := fold (fun x y => f x :: y) l [].

(** 在 Coq 中写出 [fold_map_correct] 来陈述 [fold_map] 是正确的，然后证明它。
    （提示：再次提醒，[reflexivity] 的化简力度比 [simpl] 更强。） *)

(* 请在此处解答 *)
Theorem fold_map_correct : forall X Y (f: X -> Y) (l: list X),
  fold_map f l = map f l.
Proof.
  intros X Y f l. induction l as [| h t IHl].
  - reflexivity.
  - simpl. rewrite <- IHl. reflexivity.
Qed.

(* 请勿修改下面这一行： *)
Definition manual_grade_for_fold_map : option (nat*string) := None.
(** [] *)

(** **** 练习：2 星, advanced (currying) 

    在 Coq 中，函数 [f : A -> B -> C] 的类型其实是 [A -> (B -> C)]。
    也就是说，如果给 [f] 一个类型为 [A] 的值，它就会给你函数 [f' : B -> C]。
    如果再给 [f'] 一个类型为 [B] 的值，它就会返回一个类型为 [C] 的值。
    这为我们提供了 [plus3] 中的那种偏应用能力。
    用返回函数的函数处理参数列表的方式被称为_'柯里化（Currying）'_，
    它是为了纪念逻辑学家 Haskell Curry。

    反之，我们也可以将 [A -> B -> C] 解释为 [(A * B) -> C]。这叫做
    _'反柯里化（Uncurrying）'_。对于反柯里化的二元函数，
    两个参数必须作为序对一次给出，此时它不会偏应用。 *)

(** 我们可以将柯里化定义如下： *)

Definition prod_curry {X Y Z : Type}
  (f : X * Y -> Z) (x : X) (y : Y) : Z := f (x, y).

(** 作为练习，请定义它的反函数 [prod_uncurry]，
    然后在下面证明它们互为反函数的定理。 *)

Definition prod_uncurry {X Y Z : Type}
  (f : X -> Y -> Z) (p : X * Y) : Z
:= f (fst p) (snd p).

(** 举一个柯里化用途的（平凡的）例子，我们可以用它来缩短之前看到的一个例子： *)

Example test_map1': map (plus 3) [2;0;2] = [5;3;5].
Proof. reflexivity. Qed.

(** 思考练习：在运行以下指令之前，你能计算出 [prod_curry] 和 [prod_uncurry] 
    的类型吗？ *)

Check @prod_curry : forall X Y Z : Type, (X * Y -> Z) -> X -> Y -> Z.
Check @prod_uncurry : forall X Y Z : Type, (X -> Y -> Z) -> X * Y -> Z.

Theorem uncurry_curry : forall (X Y Z : Type)
                        (f : X -> Y -> Z)
                        x y,
  prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type)
                        (f : (X * Y) -> Z) (p : X * Y),
  prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p. destruct p as [x y] eqn:Ep.
  - reflexivity.
Qed.
(** [] *)

(** **** 练习：2 星, advanced (nth_error_informal) 

    回想 [nth_error] 函数的定义：

   Fixpoint nth_error {X : Type} (l : list X) (n : nat) : option X :=
     match l with
     | [] => None
     | a :: l' => if n =? O then Some a else nth_error l' (pred n)
     end.

   请写出以下定理的非形式化证明：

   forall X l n, length l = n -> @nth_error X l n = None
*)
(* 请在此处解答 *)
(* 证：
  对 l 施加归纳法
  - 对于[]，显然 = None
  - 假设 nth_error t n = None 证明 nth_error h::t S n = None
    化简： if n =? 0 then Some h else nth_error t n = None
    由于 n = length l <> 0
    化简 nth_error t n = None
    由归纳显然成立
    原定理成立。
    *)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_informal_proof : option (nat*string) := None.
(** [] *)

(** 本练习使用_'邱奇数（Church numerals）'_探讨了另一种定义自然数的方式，
    它以数学家 Alonzo Church 命名。我们可以将自然数 [n] 表示为一个函数，
    它接受一个函数 [f] 作为参数并返回迭代了 [n] 次的 [f]。 *)

Module Church.
Definition cnat := forall X : Type, (X -> X) -> X -> X.

(** 我们来看看如何用这种记法写数。将函数迭代一次应当与将它应用一次相同。
    因此： *)

Definition one : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f x.

(** 与此类似，[two] 应当对其参数应用两次 [f]： *)

Definition two : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => f (f x).

(** 定义 [zero] 有点刁钻：我们如何“将函数应用零次”？答案很简单：
    把参数原样返回就好。 *)

Definition zero : cnat :=
  fun (X : Type) (f : X -> X) (x : X) => x.

(** 更一般地说，数 [n] 可以写作 [fun X f x => f (f
    ... (f x) ...)]，其中 [f] 出现了 [n] 次。要特别注意我们之前定义
    [doit3times] 函数的方式就是 [3] 的邱奇数表示。 *)

Definition three : cnat := @doit3times.

(** 完成以下函数的定义。请用 [reflexivity] 证明来确认它们能够通过对应的单元测试。 *)

(** **** 练习：1 星, advanced (church_succ)  *)

(** 自然数的后继：给定一个邱奇数 [n]，它的后继 [succ n] 是一个把它的参数比 [n]
    还多迭代一次的函数。 *) 

Definition succ (n : cnat) : cnat
:= fun (X : Type) (f : X -> X) (x : X) => f (n X f x).  

Example succ_1 : succ zero = one.
Proof. reflexivity. Qed.

Example succ_2 : succ one = two.
Proof. reflexivity. Qed.

Example succ_3 : succ two = three.
Proof. reflexivity. Qed.

(** [] *)

(** **** 练习：1 星, advanced (church_plus)  *)

(** 两邱奇数相加： *)
Definition plus (n m : cnat) : cnat
  := fun (X : Type) (f : X -> X) (x : X) => n X f (m X f x).

Example plus_1 : plus zero one = one.
Proof. reflexivity. Qed.

Example plus_2 : plus two three = plus three two.
Proof. reflexivity. Qed.

Example plus_3 :
  plus (plus two two) three = plus one (plus three three).
Proof. reflexivity. Qed.

(** [] *)

(** **** 练习：2 星, advanced (church_mult)  *)

(** 乘法： *)
Definition mult (n m : cnat) : cnat
  :=  fun (X : Type) (f : X -> X) (x : X) => n X (m X f) x.

Example mult_1 : mult one one = one.
Proof. reflexivity. Qed.

Example mult_2 : mult zero (plus three three) = zero.
Proof. reflexivity. Qed.

Example mult_3 : mult two three = plus three three.
Proof. reflexivity. Qed.

(** [] *)

(** **** 练习：2 星, advanced (church_exp)  *)

(** 乘方： *)

(** （_'提示'_：多态在这里起到了关键的作用。然而，棘手之处在于选择正确的类型来迭代。
    如果你遇到了「Universe inconsistency，全域不一致」错误，请在不同的类型上迭
    代。在 [cnat] 本身上迭代通常会有问题。） *)

Definition exp (n m : cnat) : cnat
  := fun (X : Type) (f : X -> X) (x : X) => m (X -> X) (n X) f x.

Example exp_1 : exp two two = plus two two.
Proof. reflexivity. Qed.

Example exp_2 : exp three zero = one.
Proof. reflexivity. Qed.

Example exp_3 : exp three two = plus (mult two (mult two two)) one.
Proof. reflexivity. Qed.

(** [] *)

End Church.

End Exercises.


(* 2022-03-14 05:26:56 (UTC+00) *)
