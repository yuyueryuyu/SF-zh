(** * IndProp: 归纳定义的命题 *)

Set Warnings "-notation-overridden,-parsing".
From LF Require Export Logic.

(* ################################################################# *)
(** * 归纳定义的命题 *)

(** 在 [Logic] 一章中，我们学习了多种方式来书写命题，包括合取、析取和存在量词。
    在本章中，我们引入另一种新的方式：_'归纳定义（Inductive Definitions）'_。

    _'注意'_：为简单起见，本章中的大部分内容都用一个归纳定义的“偶数性”作为展示的例子。
    你可能会为此感到不解，因为我们已经有一种将偶数性定义为命题的完美方法了（若
    [n] 等于某个整数的二倍，那么它是是偶数）。尚若如此，那么请放心，
    在本章末尾和以后的章节中，我们会看到更多引人入胜的归纳定义的命题示例。 *)

(** 在前面的章节中，我们已经见过两种表述 [n] 为偶数的方式了：

      (1) [evenb n = true]，以及

      (2) [exists k, n = double k]。

    然而还有一种方式是通过如下规则来建立 [n] 的偶数性质：

       - 规则 [ev_0]: [0] 是偶数。
       - 规则 [ev_SS]: 如果 [n] 是偶数, 那么 [S (S n)] 也是偶数。 *)

(** 为了理解这个新的偶数性质定义如何工作，我们可想象如何证明 [4] 是偶数。
    根据规则 [ev_SS]，需要证明 [2] 是偶数。这时，只要证明 [0] 是偶数，
    我们可继续通过规则 [ev_SS] 确保它成立。而使用规则 [ev_0] 可直接证明 [0] 是偶数。*)

(** 接下来的课程中，我们会看到很多类似方式定义的命题。
    在非形式化的讨论中，使用简单的记法有助于阅读和书写。
    _'推断规则（Inference Rules）'_就是其中的一种。
    （我们为此性质取名为 [ev]，因为 [even] 已经用过了。）

                              ------------             (ev_0)
                                 ev 0

                                 ev n
                            ----------------          (ev_SS)
                             ev (S (S n))
*)

(**
    若将上面的规则重新排版成推断规则，我们可以这样阅读它，如果线上方的
    _'前提（Premises）'_成立，那么线下方的_'结论（Conclusion）'_成立。
    比如，规则 [ev_SS] 读做如果 [n] 满足 [even]，那么 [S (S n)] 也满足。
    如果一条规则在线上方没有前提，则结论直接成立。

    我们可以通过组合推断规则来展示证明。下面展示如何转译 [4] 是偶数的证明：

                             --------  (ev_0)
                              ev 0
                             -------- (ev_SS)
                              ev 2
                             -------- (ev_SS)
                              ev 4
*)

(** （为什么我们把这样的证明称之为“树”而非其他，比如“栈”？
    因为一般来说推断规则可以有多个前提。我们很快就会看到一些例子。 *)

(* ================================================================= *)
(** ** 偶数性的归纳定义

    基于上述，可将偶数性质的定义翻译为在 Coq 中使用 [Inductive] 声明的定义，
    声明中每一个构造子对应一个推断规则： *)

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS (n : nat) (H : ev n) : ev (S (S n)).

(** 这个定义与之前 [Inductive] 定义的用法有一个有趣的区别：一方面，
    我们定义的并不是一个 [Type]（如 [nat]），而是一个将 [nat] 映射到 [Prop]
    的函数——即关于数的性质。然而真正要关注的是，由于 [ev] 中的 [nat]
    参数出现在冒号_'右侧'_，这允许在不同的构造子类型中使用不同的值：例如
    [ev_0] 类型中的 [0] 以及 [ev_SS] 类型中的 [S (S n)]。与此相应，
    每个构造子的类型必须在冒号后显式指定，并且对于某个自然数 [n]
    来说，每个构造子的类型都必须有 [ev n] 的形式。

    相反，回忆 [list] 的定义：

    Inductive list (X:Type) : Type :=
      | nil
      | cons (x : X) (l : list X).

    它以_'全局的方式'_在冒号_'左侧'_引入了参数 [X]，
    强迫 [nil] 和 [cons] 的结果为同一个类型（[list X]）。
    如果在定义 [ev] 时将 [nat] 置于冒号左侧，就会得到如下错误： *)

Fail Inductive wrong_ev (n : nat) : Prop :=
| wrong_ev_0 : wrong_ev 0
| wrong_ev_SS (H: wrong_ev n) : wrong_ev (S (S n)).
(* ===> Error: Last occurrence of "[wrong_ev]" must have "[n]"
        as 1st argument in "[wrong_ev 0]". *)

(** 在 [Inductive] 定义中，类型构造子冒号左侧的参数叫做形参（Parameter），
    而右侧的叫做索引（Index）或注解（Annotation）。

    例如，在 [Inductive list (X : Type) := ...] 中，[X] 是一个形参；而在
    [Inductive ev : nat -> Prop := ...] 中，未命名的 [nat] 参数是一个索引。 *)

(** 在 Coq 中，我们可以认为 [ev] 定义了一个性质 [ev : nat -> Prop]，其包括
    “证据构造子” [ev_0 : ev 0] 和 [ev_SS : forall n, ev n -> ev (S (S n))]。 *)

(** 这些 “证据构造子” 等同于已经证明过的定理。
    具体来说，我们可以使用 Coq 中的 [apply] 策略和规则名称来证明某个数的 [ev] 性质…… *)

Theorem ev_4 : ev 4.
Proof. apply ev_SS. apply ev_SS. apply ev_0. Qed.

(** ……或使用函数应用的语法： *)

Theorem ev_4' : ev 4.
Proof. apply (ev_SS 2 (ev_SS 0 ev_0)). Qed.

(** 我们同样可以对前提中使用到 [ev] 的定理进行证明。 *)

Theorem ev_plus4 : forall n, ev n -> ev (4 + n).
Proof.
  intros n. simpl. intros Hn.
  apply ev_SS. apply ev_SS. apply Hn.
Qed.

(** 更一般地，我们可以证明以任意数乘 2 是偶数： *)

(** **** 练习：1 星, standard (ev_double)  *)
Theorem ev_double : forall n,
  ev (double n).
Proof.
  intros n. induction n as [| n' IHn'].
  - simpl. apply ev_0.
  - simpl. apply ev_SS. apply IHn'.
Qed.   
(** [] *)

(* ################################################################# *)
(** * 在证明中使用证据 *)

(** 除了_'构造'_证据（evidence）来表示某个数是偶数，我们还可以_'解构'_这样的证据，
    这等于对它的构造进行论证。

    对 [ev] 而言，使用 [Inductive] 声明来引入 [ev] 会告诉 Coq，
    [ev_0] 和 [ev_SS] 构造子不仅是构造偶数证明证据的有效方式，
    还是构造一个数满足 [ev] 的证据的_'唯一'_方式。 *)

(** 换句话说，如果某人展示了对于 [ev n] 的证据 [E]，那么我们知道 [E]
    必是二者其一：

      - [E] 是 [ev_0]（且 [n] 为 [O]），或
      - [E] 是 [ev_SS n' E']（且 [n] 为 [S (S n')]，[E'] 为
        [ev n'] 的证据）. *)

(** 这样的形式暗示着，我们可以像分析归纳定义的数据结构一样分析形如 [ev n]
    的假设；特别地，对于这类证据使用_'归纳（induction）'_和_'分类讨论（case
    analysis）'_来进行论证也是可行的。让我们通过一些例子来学习实践中如何使用他们。 *)

(* ================================================================= *)
(** ** 对证据进行反演 *)

(** Suppose we are proving some fact involving a number [n], and
    we are given [ev n] as a hypothesis.  We already know how to
    perform case analysis on [n] using [destruct] or [induction],
    generating separate subgoals for the case where [n = O] and the
    case where [n = S n'] for some [n'].  But for some proofs we may
    instead want to analyze the evidence that [ev n] _directly_. As
    a tool, we can prove our characterization of evidence for
    [ev n], using [destruct]. *)

Theorem ev_inversion :
  forall (n : nat), ev n ->
    (n = 0) \/ (exists n', n = S (S n') /\ ev n').
Proof.
  intros n E.
  destruct E as [ | n' E'].
  - (* E = ev_0 : ev 0 *)
    left. reflexivity.
  - (* E = ev_SS n' E' : ev (S (S n')) *)
    right. exists n'. split. reflexivity. apply E'.
Qed.

(** 用 [destruct] 解构证据即可证明下述定理： *)

Theorem ev_minus2 : forall n,
  ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  destruct E as [| n' E'].
  - (* E = ev_0 *) simpl. apply ev_0.
  - (* E = ev_SS n' E' *) simpl. apply E'.
Qed.

(** However, this variation cannot easily be handled with just
    [destruct]. *)

Theorem evSS_ev : forall n,
  ev (S (S n)) -> even n.
(** 直观来说，我们知道支撑前提的证据不会由 [ev_0] 组成，因为 [0] 和 [S] 是
    [nat] 类型不同的构造子；由此 [ev_SS] 是唯一需要应对的情况（译注：[ev_0] 无条件成立）。
    不幸的是，[destruct] 并没有如此智能，它仍然为我们生成两个子目标。
    更坏的是，于此同时最终目标没有改变，也无法为完成证明提供任何有用的信息。 *)

Proof.
  intros n E.
  destruct E as [| n' E'] eqn:EE.
  - (* E = ev_0. *)
    (* 我们须证明 [n] 是偶数，但没有任何有用的假设信息可以使用！ *)
Abort.

(** 究竟发生了什么？应用 [destruct] 把性质的参数替换为对应于构造子的值。
    这对于证明 [ev_minus2'] 是有帮助的，因为在最终目标中直接使用到了参数 [n]。
    然而，这对于 [evSS_ev] 并没有帮助，因为被替换掉的 [S (S n)] 并没有在其他地方被使用。*)

(** If we [remember] that term [S (S n)], the proof goes
    through.  (We'll discuss [remember] in more detail below.) *)

Theorem evSS_ev_remember : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n H. remember (S (S n)) as k. destruct H as [|n' E'].
  - (* E = ev_0 *)
    (* Now we do have an assumption, in which [k = S (S n)] has been
       rewritten as [0 = S (S n)] by [destruct]. That assumption
       gives us a contradiction. *)
    discriminate Heqk.
  - (* E = ev_S n' E' *)
    (* This time [k = S (S n)] has been rewritten as [S (S n') = S (S n)]. *)
    injection Heqk as Heq. rewrite Heq in E'. apply E'.
Qed.

(** Alternatively, the proof is straightforward using our inversion
    lemma. *)

Theorem evSS_ev : forall n, ev (S (S n)) -> ev n.
Proof. intros n H. apply ev_inversion in H. destruct H.
 - discriminate H.
 - destruct H as [n' [Hnm Hev]]. injection Hnm as Heq.
   rewrite Heq. apply Hev.
Qed.

(** Note how both proofs produce two subgoals, which correspond
    to the two ways of proving [ev].  The first subgoal is a
    contradiction that is discharged with [discriminate].  The second
    subgoal makes use of [injection] and [rewrite].  Coq provides a
    handy tactic called [inversion] that factors out that common
    pattern.

    The [inversion] tactic can detect (1) that the first case ([n =
    0]) does not apply and (2) that the [n'] that appears in the
    [ev_SS] case must be the same as [n].  It has an "[as]" variant
    similar to [destruct], allowing us to assign names rather than
    have Coq choose them. *)

Theorem evSS_ev' : forall n,
  ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [| n' E' EQ].
  (* We are in the [E = ev_SS n' E'] case now. *)
  apply E'.
Qed.

(** The [inversion] tactic can apply the principle of explosion to
    "obviously contradictory" hypotheses involving inductively defined
    properties, something that takes a bit more work using our
    inversion lemma. For example: *)

Theorem one_not_even : ~ ev 1.
Proof.
  intros H. apply ev_inversion in H.
  destruct H as [ | [m [Hm _]]].
  - discriminate H.
  - discriminate Hm.
Qed.

Theorem one_not_even' : ~ ev 1.
  intros H. inversion H. Qed.

(** **** 练习：1 星, standard (inversion_practice) 

    利用 [inversion] 策略证明以下结论。（如想进一步练习，请使用反演定理证明之。） *)

Theorem SSSSev__even : forall n,
  ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n H. inversion H as [| n' H' IH'].
  inversion H' as [| n'' H'' IH''].
  apply H''.
Qed.
(** [] *)

(** **** 练习：1 星, standard (ev5_nonsense) 

    请使用 [inversion] 策略证明以下结果。 *)

Theorem ev5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros H. inversion H. inversion H1. inversion H3.
Qed.
(** [] *)

(** The [inversion] tactic does quite a bit of work. For
    example, when applied to an equality assumption, it does the work
    of both [discriminate] and [injection]. In addition, it carries
    out the [intros] and [rewrite]s that are typically necessary in
    the case of [injection]. It can also be applied, more generally,
    to analyze evidence for inductively defined propositions.  As
    examples, we'll use it to reprove some theorems from chapter
    [Tactics].  (Here we are being a bit lazy by omitting the [as]
    clause from [inversion], thereby asking Coq to choose names for
    the variables and hypotheses that it introduces.) *)

Theorem inversion_ex1 : forall (n m o : nat),
  [n; m] = [o; o] ->
  [n] = [m].
Proof.
  intros n m o H. inversion H. reflexivity. Qed.

Theorem inversion_ex2 : forall (n : nat),
  S n = O ->
  2 + 2 = 5.
Proof.
  intros n contra. inversion contra. Qed.

(** [inversion] 的工作原理大致如下：假设 [H] 指代上下文中的假设 [P]，
    且 [P] 由 [Inductive] 归纳定义，则对于 [P] 每一种可能的构造，[inversion H]
    各为其生成子目标。子目标中自相矛盾者被忽略，证明其余子命题即可得证原命题。
    在证明子目标时，上下文中的 [H] 会替换为 [P] 的构造条件，
    即其构造子所需参数以及必要的等式关系。例如：倘若 [ev n] 由 [evSS] 构造，
    上下文中会引入参数 [n']、[ev n']，以及等式 [S (S n') = n]。 *)

(** 上面的 [ev_double] 练习展示了偶数性质的一种新记法，其被之前的两种记法所蕴含。
    （因为，由  [Logic] 一章中的 [even_bool_prop]，我们已经知道
    他们是互相等价的。）
    为了展示这三种方式的一致性，我们需要下面的引理： *)

Lemma ev_even_firsttry : forall n,
  ev n -> even n.
Proof.
  (* 课上已完成 *)

(** 我们可以尝试使用分类讨论或对 [n] 进行归纳。但由于 [ev]
    在前提中出现，所以和前面章节的一些例子一样，这种策略行不通，
    因为如前面提到的，归纳法则会讨论 n-1，而它并不是偶数！
    如此我们似乎可以先试着对 [ev] 的证据进行反演。
    确实，第一个分类可以被平凡地证明。 *)

  intros n E. inversion E as [EQ' | n' E' EQ'].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E' *) simpl.

(** 然而第二个分类要困难一些。我们需要证明 [exists k, S (S n') = double k]，
    但唯一可用的假设是 [E']，也即 [ev n'] 成立。但这对证明并没有帮助，
    我们似乎被卡住了，而对 [E] 进行分类讨论是徒劳的。

    如果仔细观察第二个（子）目标，我们可以发现一些有意思的事情：
    对 [E] 进行分类讨论，我们可以把要证明的原始目标归约到另一个上，
    其涉及到另一个 [ev] 的证据： [E']。
    形式化地说，我们可以通过展示如下证据来完成证明：

        exists k', n' = double k',

    这同原始的命题是等价的，只是 [n'] 被替换为 n。确实，通过这个中间结果完成证明
    并不困难。  *)

    assert (I : (exists k', n' = double k') ->
                (exists k, S (S n') = double k)).
    { intros [k' Hk']. rewrite Hk'. exists (S k'). reflexivity. }
    apply I. (* 将原始目标归约到新目标上 *)

    (* However, at this point we can go no further. *)
Abort.

(* ================================================================= *)
(** ** 对证据进行归纳 *)

(** 上面的情形看起来似曾相识，但这并非巧合。在 [Induction]
    一章中，我们曾试着用分类讨论来证明其实需要归纳才能证明的命题。
    这一次，解决方法仍然是……使用归纳！ *)

(** 对证据和对数据使用 [induction] 具有同样的行为：它导致 Coq
    对每个可用于构造证据的构造子生成一个子目标，同时对递归出现的问题性质提供了归纳假设。

    To prove a property of [n] holds for all numbers for which [ev
    n] holds, we can use induction on [ev n]. This requires us to
    prove two things, corresponding to the two ways in which [ev n]
    could have been constructed. If it was constructed by [ev_0], then
    [n=0], and the property must hold of [0]. If it was constructed by
    [ev_SS], then the evidence of [ev n] is of the form [ev_SS n'
    E'], where [n = S (S n')] and [E'] is evidence for [ev n']. In
    this case, the inductive hypothesis says that the property we are
    trying to prove holds for [n']. *)

(** 让我们再次尝试证明这个引理： *)

Lemma ev_even : forall n,
  ev n -> even n.
Proof.
  intros n E.
  induction E as [|n' E' IH].
  - (* E = ev_0 *)
    exists 0. reflexivity.
  - (* E = ev_SS n' E'
       同时 IH : exists k', n' = double k' *)
    destruct IH as [k' Hk'].
    rewrite Hk'. exists (S k'). reflexivity.
Qed.

(** 这里我们看到 Coq 对 [E'] 产生了 [IH]，而 [E'] 是唯一递归出现的
    [ev] 命题。 由于 [E'] 中涉及到 [n']，这个归纳假设是关于 [n'] 的，
    而非关于 [n] 或其他数字的。  *)

(** 关于偶数性质的第二个和第三个定义的等价关系如下： *)

Theorem ev_even_iff : forall n,
  ev n <-> even n.
Proof.
  intros n. split.
  - (* -> *) apply ev_even.
  - (* <- *) intros [k Hk]. rewrite Hk. apply ev_double.
Qed.

(** 我们会在后面的章节中看到，对证据进行归纳在很多领域里是一种常用的技术，
    特别是在形式化程序语言的语义时，由于其中很多有趣的性质都是归纳定义的。 *)

(** 下面的练习提供了一些简单的例子，来帮助你熟悉这项技术。 *)

(** **** 练习：2 星, standard (ev_sum)  *)
Theorem ev_sum : forall n m, ev n -> ev m -> ev (n + m).
Proof.
  intros n m Hn Hm. induction Hn as [|n' Hn' IHn'].
  - simpl. apply Hm.
  - simpl. apply ev_SS. apply IHn'.
Qed.    
(** [] *)

(** **** 练习：4 星, advanced, optional (ev'_ev) 

    一般来说，有很多种方式来归纳地定义一个性质。比如说，下面是关于
    [ev] 的另一种（蹩脚的）定义：*)

Inductive ev' : nat -> Prop :=
| ev'_0 : ev' 0
| ev'_2 : ev' 2
| ev'_sum n m (Hn : ev' n) (Hm : ev' m) : ev' (n + m).

(** 请证明这个定义在逻辑上等同于前述定义。为了精简证明，请使用 [Logic]
    一章中将定理应用到参数的技术，注意同样的技术也可用于归纳定义的命题的构造子。 *)

Theorem ev'_ev : forall n, ev' n <-> ev n.
Proof.
  intros n. split.
  - intros H. induction H as [| | n' m' Hn Hm IHn IHm].
    + apply ev_0. 
    + apply ev_SS. apply ev_0.
    + apply ev_sum.
      * apply Hm.
      * apply IHm.
  - intros H. induction H as [| n' Hn IHn].
    + apply ev'_0.
    + apply (ev'_sum 2 n').
      * apply ev'_2.
      * apply IHn.
Qed.        
(** [] *)

(** **** 练习：3 星, advanced, recommended (ev_ev__ev) 

    这里有两个可以试着在其上进行归纳的证据，一个不行就换另一个。 *)

Theorem ev_ev__ev : forall n m,
  ev (n+m) -> ev n -> ev m.
Proof.
  intros n m H0 H1. induction H1 as [| n' Hn' IHn'].
  - simpl in H0. apply H0.
  - simpl in H0. apply IHn'. apply evSS_ev. apply H0.
Qed.   
(** [] *)

(** **** 练习：3 星, standard, optional (ev_plus_plus) 

    本练习只需要使用前述引理，而无需使用归纳或分类讨论，
    虽然一些改写可能会比较乏味。 *)

Theorem ev_plus_plus : forall n m p,
  ev (n+m) -> ev (n+p) -> ev (m+p).
Proof.
  intros n m p H1 H2. apply (ev_sum (n+p)) in H1.
  - rewrite plus_assoc in H1. rewrite (plus_comm (n+p) (n)) in H1. 
    rewrite plus_assoc in H1. rewrite <- plus_assoc in H1. 
    apply (ev_ev__ev (n+n) (p+m)) in H1.
    + rewrite plus_comm in H1. apply H1.
    + apply ev_even_iff. exists n. symmetry. apply double_plus.
  - apply H2. 
Qed.
(** [] *)

(* ################################################################# *)
(** * 归纳关系 *)

(** 我们可以认为被一个数所参数化的命题（比如 [ev]）是一个_'性质'_，也即，
    它定义了 [nat]　的一个子集，其中的数可以被证明满足此命题。
    以同样的方式，我们可认为有两个参数的命题是一个_'关系'_，也即，它定义了一个
    可满足此命题的序对集合。*)

Module Playground.

(** 和命题一样，关系也可以归纳地定义。一个很有用的例子是整数的“小于等于”关系。*)

(** 下面的定义应当是比较直观的。它提供了两种方法来描述一个数小于等于另一个数的证据：
    要么可观察到两个数相等，或提供证据显示第一个数小于等于第二个数的前继。　*)

Inductive le : nat -> nat -> Prop :=
  | le_n (n : nat)                : le n n
  | le_S (n m : nat) (H : le n m) : le n (S m).

Notation "m <= n" := (le m n).

(** 类似于证明 [ev] 这样的性质，使用 [le_n] 和 [le_S] 构造子来证明关于 [<=]
    的事实遵循了同样的模式。我们可以对构造子使用 [apply] 策略来证明 [<=] 目标
    （比如证明 [3<=3] 或 [3<=6]），也可以使用 [inversion] 策略来从上下文中 [<=]
    的假设里抽取信息（比如证明 [(2<=1) -> 2+2=5]）。 *)

(** 这里提供一些完备性检查。（请注意，尽管这同我们在开始课程时编写的
    函数“单元测试”类似，但我们在这里必须明确地写下他们的证明——[simpl] 和
    [reflexivity] 并不会有效果，因为这些证明不仅仅是对表达式进行简化。）  *)

Theorem test_le1 :
  3 <= 3.
Proof.
  (* 课上已完成 *)
  apply le_n.  Qed.

Theorem test_le2 :
  3 <= 6.
Proof.
  (* 课上已完成 *)
  apply le_S. apply le_S. apply le_S. apply le_n.  Qed.

Theorem test_le3 :
  (2 <= 1) -> 2 + 2 = 5.
Proof.
  (* 课上已完成 *)
  intros H. inversion H. inversion H2.  Qed.

(** 现在“严格小于”关系 [n < m] 可以使用 [le] 来定义。 *)

End Playground.

Definition lt (n m:nat) := le (S n) m.

Notation "m < n" := (lt m n).

(** 这里展示了一些定义于自然数上的关系：*)

Inductive square_of : nat -> nat -> Prop :=
  | sq n : square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
  | nn n : next_nat n (S n).

Inductive next_ev : nat -> nat -> Prop :=
  | ne_1 n (H: ev (S n))     : next_ev n (S n)
  | ne_2 n (H: ev (S (S n))) : next_ev n (S (S n)).

(** **** 练习：2 星, standard, optional (total_relation) 

    请定一个二元归纳关系 [total_relation] 对每一个自然数的序对成立。 *)

(* 请在此处解答

    [] *)
Inductive total_relation : nat -> nat -> Prop :=
  | tot n m : total_relation n m.

Theorem total_relation_true : forall (n m : nat),
  total_relation n m.
Proof.
  intros n m.
  apply (tot n m).
Qed.

(** **** 练习：2 星, standard, optional (empty_relation) 

    请定一个二元归纳关系 [empty_relation] 对自然数永远为假。 *)

(* 请在此处解答

    [] *)
Inductive empty_relation_other : nat -> nat -> Prop :=
  .
(* 以上这个定义由于没有构造子，所以对所有n m永远为假。  
   初始答案为下方这个定义。一开始没有想到，在这里进行记录 *)
Inductive empty_relation : nat -> nat -> Prop :=
  | ept n m (H: False): empty_relation n m.

Theorem empty_relation_true : forall (n m : nat),
  ~(empty_relation n m).
Proof.
  intros n m. unfold not. intros H. inversion H. apply H0.
Qed.

(** From the definition of [le], we can sketch the behaviors of
    [destruct], [inversion], and [induction] on a hypothesis [H]
    providing evidence of the form [le e1 e2].  Doing [destruct H]
    will generate two cases. In the first case, [e1 = e2], and it
    will replace instances of [e2] with [e1] in the goal and context.
    In the second case, [e2 = S n'] for some [n'] for which [le e1 n']
    holds, and it will replace instances of [e2] with [S n'].
    Doing [inversion H] will remove impossible cases and add generated
    equalities to the context for further use. Doing [induction H]
    will, in the second case, add the induction hypothesis that the
    goal holds when [e2] is replaced with [n']. *)

(** **** 练习：3 星, standard, optional (le_exercises) 

    这里展示一些 [<=] 和 [<] 关系的事实，我们在接下来的课程中将会用到他们。
    证明他们将会是非常有益的练习。 *)

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o H1 H2. generalize dependent m.
  induction H2 as [| o' Ho' IHo'].
  - intros m H1. apply H1.
  - intros m H1. apply le_S. apply IHo'. apply H1.        
Qed.

Theorem O_le_n : forall n,
  0 <= n.
Proof.
  intros n. induction n as [| n' IHn'].
  - apply le_n.
  - apply (le_trans 0 n' (S n')).
    + apply IHn'.
    + apply le_S. apply le_n.
Qed.   

Theorem n_le_m__Sn_le_Sm : forall n m,
  n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
  - apply le_n.
  - apply le_S. apply IHle.
Qed.   

Theorem Sn_le_Sm__n_le_m : forall n m,
  S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  - apply le_n.
  - apply (le_trans n (S n) m).
    + apply le_S. apply le_n.
    + apply H1.
Qed.           

Theorem le_plus_l : forall a b,
  a <= a + b.
Proof.
  intros a b. induction b.
  - rewrite <- plus_n_O. apply le_n.
  - apply (le_trans a (a+b) (a+S b)).
    + apply IHb.
    + rewrite <- plus_n_Sm. apply le_S. apply le_n.
Qed.   

Theorem plus_le : forall n1 n2 m,
  n1 + n2 <= m ->
  n1 <= m /\ n2 <= m.
Proof.
  intros n1 n2 m H. split.
  - apply (le_trans n1 (n1+n2) m).
    + apply le_plus_l.
    + apply H.
  - apply (le_trans n2 (n1+n2) m).
    + rewrite plus_comm. apply le_plus_l.
    + apply H.
Qed.    

(** Hint: the next one may be easiest to prove by induction on [n]. *)

Theorem add_le_cases : forall n m p q,
    n + m <= p + q -> n <= p \/ m <= q.
Proof.
  intros n m p q H. 
  induction n as [| n' IHn].
  - left. apply O_le_n.
  - destruct IHn as [IHn1 | IHn2].
    + rewrite plus_comm in H. rewrite <- plus_n_Sm in H.
      apply (plus_le 1 (m+n') (p+q)) in H.
      destruct H as [H1 H2].
      rewrite plus_comm in H2.
      apply H2.
    + destruct IHn1.
      * right. rewrite plus_comm in H.
        rewrite <- plus_n_Sm in H. rewrite plus_comm in H.
        rewrite -> plus_n_Sm in H. induction n'.
        { rewrite plus_comm in H. rewrite <- plus_n_O in H.
          rewrite plus_comm in H. rewrite <- plus_n_O in H.
          apply le_S in H. apply Sn_le_Sm__n_le_m. apply H. }
        { apply IHn'. apply Sn_le_Sm__n_le_m. rewrite plus_comm.
          rewrite plus_n_Sm. rewrite plus_comm.
          rewrite (plus_comm n' q). rewrite plus_n_Sm.
          rewrite (plus_comm q (S n')). apply H. }
      * left. apply n_le_m__Sn_le_Sm. apply IHn1.
    + right. apply IHn2.  
Qed.

Theorem lt_S : forall n m,
  n < m ->
  n < S m.
Proof.
  intros n m H. unfold lt. unfold lt in H. apply le_S in H. apply H.
Qed.

Theorem plus_lt : forall n1 n2 m,
  n1 + n2 < m ->
  n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m. unfold lt. intros H. split.
  - rewrite plus_comm in H. rewrite plus_n_Sm in H. apply plus_le in H.
    destruct H as [H1 H2]. apply H2.
  - rewrite plus_n_Sm in H. apply plus_le in H. destruct H as [H1 H2].
    apply H2.
Qed.   

Theorem leb_complete : forall n m,
  n <=? m = true -> n <= m.
Proof.
  intros n. induction n as [| n' IHn'].
  - intros m H. apply O_le_n.
  - intros m H. destruct m as [| m'] eqn:Em.
    + simpl in H. discriminate H.
    + simpl in H. apply n_le_m__Sn_le_Sm. apply IHn'. apply H.
Qed.    

(** 提示：在下面的问题中，对 [m] 进行归纳会使证明容易一些。*)

Theorem leb_correct : forall n m,
  n <= m ->
  n <=? m = true.
Proof.
  intros n m H. generalize dependent n. induction m as [| m' IHm'].
  - intros n H. inversion H.
    + reflexivity.
  - intros n H. destruct n as [| n'] eqn:En.
    + simpl. reflexivity.
    + simpl. apply IHm'. apply Sn_le_Sm__n_le_m. apply H.
Qed.     

(** 提示：以下定理可以不使用 [induction] 而证明。*)

Theorem leb_true_trans : forall n m o,
  n <=? m = true -> m <=? o = true -> n <=? o = true.
Proof.
  intros n m o H1 H2. apply leb_complete in H1. apply leb_complete in H2.
  apply leb_correct. apply (le_trans n m o).
  - apply H1.
  - apply H2.
Qed.  
(** [] *)

(** **** 练习：2 星, standard, optional (leb_iff)  *)
Theorem leb_iff : forall n m,
  n <=? m = true <-> n <= m.
Proof.
  intros n m. split.
  - apply leb_complete.
  - apply leb_correct.
Qed. 
(** [] *)

Module R.

(** **** 练习：3 星, standard, recommended (R_provability) 

    通过同样的方式，我们可以定义三元关系、四元关系等。例如，考虑以下定义在自然数上的三元关系： *)

Inductive R : nat -> nat -> nat -> Prop :=
   | c1 : R 0 0 0
   | c2 m n o (H : R m n o) : R (S m) n (S o)
   | c3 m n o (H : R m n o) : R m (S n) (S o)
   | c4 m n o (H : R (S m) (S n) (S (S o))) : R m n o
   | c5 m n o (H : R m n o) : R n m o.

(** - 下列哪个命题是可以被证明的？
      - [R 1 1 2]
      - [R 2 2 6]

    - 如果在 [R] 的定义中我们丢弃 [c5] 构造子，可被证明的集合会发生变化吗？
      简要（一句话）解释你的答案。

    - 如果在 [R] 的定义中我们丢弃 [c4] 构造子，可被证明的集合会发生变化吗？
      简要（一句话）解释你的答案。 *)

(* 请在此处解答 *)
Example R_ex1 : R 1 1 2.
Proof. 
  apply (c3 1 0 1). apply (c2 0 0 0). apply c1.
Qed.

(* [R 2 2 6] 不可被证明，要证明关于R的命题，必须满足m+n=o.
  c1 : R 0 0 0 默认成立
  c2 可以让 m 和 o 同时-1
  c3 可以让 n 和 o 同时-1
  c4 可以让 m n 分别+1 o+2
  c5 可以交换m n的值
  注意到五个规则都无法改变m+n和o的关系，因此若m+n!=o，则R 0 0 0永远无法达成。 *)
(* 丢弃c4 c5不会改变。上面说到可证明的命题需要满足m+n=o，去掉c4和c5都不影响命题数字向0减少。*) 
(*  *)
(* 请勿修改下面这一行： *)
Definition manual_grade_for_R_provability : option (nat*string) := None.
(** [] *)

(** **** 练习：3 星, standard, optional (R_fact) 

    关系 [R] 其实编码了一个熟悉的函数。请找出这个函数，定义它并在 Coq 中证明他们等价。*)

Definition fR : nat -> nat -> nat
  := plus.

Lemma R_O_n_n : forall n, R 0 n n.
Proof.
  intros n. induction n as [| n' IHn'].
  - apply c1.
  - apply c3. apply IHn'.
Qed.  

Theorem R_equiv_fR : forall m n o, R m n o <-> fR m n = o.
Proof.
  intros m n o. unfold fR. split.
  - intros H. induction H.
    + reflexivity.
    + simpl. f_equal. apply IHR.
    + rewrite <- plus_n_Sm. f_equal. apply IHR.
    + simpl in IHR. injection IHR as IH.
      rewrite <- plus_n_Sm in IH. injection IH as IH'. apply IH'.
    + rewrite plus_comm. apply IHR.
  - generalize dependent o. induction m as [| m' IHm'].
    + intros o H. rewrite plus_O_n in H. rewrite H. apply R_O_n_n.
    + intros o H. destruct o as [| o'] eqn:Eo.
      * discriminate H.
      * apply c2. rewrite plus_comm in H. rewrite <- plus_n_Sm in H.
        injection H as H'. apply IHm'. rewrite plus_comm.
        apply H'.
Qed. 

(** [] *)

End R.

(** **** 练习：2 星, advanced (subsequence) 

    如果一个列表的所有元素以相同的顺序出现在另一个列表之中（但允许其中出现其他额外的元素），
    我们把第一个列表称作第二个列表的_'子序列'_。 例如：

      [1;2;3]

    是以下所有列表的子序列

      [1;2;3]
      [1;1;1;2;2;3]
      [1;2;7;3]
      [5;6;1;9;9;2;7;3;8]

    但_'不是'_以下列表的子序列

      [1;2]
      [1;3]
      [5;6;2;1;7;3;8].

    - 在 [list nat] 上定一个归纳命题 [subseq]，其表达了子序列的涵义。
      （提示：你需要三个分类。）

    - 证明子序列的自反关系 [subseq_refl]，也即任何列表是它自身的子序列。

    - 证明关系 [subseq_app] 对任意列表 [l1]，[l2] 和 [l3]，如果 [l1] 是 [l2]
      的子序列，那么 [l1] 也是 [l2 ++ l3] 的子序列。

    - （可选的，困难）证明子序列的传递关系 [subseq_trans]——也即，如果 [l1] 是 [l2]
      的子序列，且 [l2] 是 [l3] 的子序列，那么 [l1] 是 [l3] 的子序列。
      （提示：仔细选择进行归纳的项！） *)

Inductive subseq : list nat -> list nat -> Prop :=
  | subseq_same l2: subseq [] l2 
  | subseq_l1 (l1: list nat) (h2: nat) (t2: list nat) (H: subseq l1 t2) : subseq l1 (h2::t2)
  | subseq_h_t (t1:list nat) (t2:list nat) (h: nat) (H: subseq t1 t2) : subseq (h::t1) (h::t2)
.

Theorem subseq_refl : forall (l : list nat), subseq l l.
Proof.
  intros l. induction l as [| h t IHl].
  - apply subseq_same. 
  - apply subseq_h_t. apply IHl.
Qed.  

Theorem subseq_app : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l1 (l2 ++ l3).
Proof.
  intros l1 l2 l3 H. induction H as [|l1' h' t' Hl' IHl'| h1' t1' h2' t2' Hl']. 
  - apply subseq_same.
  - simpl. apply subseq_l1. apply IHl'.
  - simpl. apply subseq_h_t. apply Hl'.
Qed.

Theorem subseq_trans : forall (l1 l2 l3 : list nat),
  subseq l1 l2 ->
  subseq l2 l3 ->
  subseq l1 l3.
Proof.
  intros l1 l2 l3 H1 H2. generalize dependent l1. induction H2 as [|l2' |].
  - intros l1 H1. inversion H1. apply subseq_same.
  - intros l1 H1. apply subseq_l1. apply IHsubseq. apply H1.
  - intros l1 H1. inversion H1.
    + apply subseq_same.
    + apply subseq_l1. apply IHsubseq. apply H3.
    + apply subseq_h_t. apply IHsubseq. apply H3.
Qed.
(** [] *)

(** **** 练习：2 星, standard, optiona l (R_provability2) 

    假设我们在 Coq 中有如下定义：

    Inductive R : nat -> list nat -> Prop :=
      | c1 : R 0 []
      | c2 n l (H: R n l) : R (S n) (n :: l)
      | c3 n l (H: R (S n) l) : R n l.

    下列命题哪个是可被证明的？

    - [R 2 [1;0]]
    - [R 1 [1;2;1;0]]
    - [R 6 [3;2;1;0]]  *)

(* 请在此处解答
第一个可以证明。
第二个无法证明。 因为首先列表不能被改变，且n在无法通过c2规约的时候只能增加，
1只能被0用c2归约，所以无法被证明
第三个无法被证明，和第二个理由相同。
    [] *)

Inductive R : nat -> list nat -> Prop :=
| c1 : R 0 []
| c2 n l (H: R n l) : R (S n) (n :: l)
| c3 n l (H: R (S n) l) : R n l.

Example R_1: R 2 [1;0].
Proof. apply c2. apply c2. apply c1. Qed. 

(* ################################################################# *)
(** * 案例学习：正则表达式 *)

(** 性质 [ev] 提供了一个简单的例子来展示归纳定义和其基础的推理技巧，
    但这还不是什么激动人心的东西——毕竟，[even] 等价于我们之前见过的两个非归纳的定义，
    而看起来归纳定义并没有提供什么好处。为了更好地展示归纳定义的表达能力，
    我们继续使用它来建模计算机科学中的一个经典概念——正则表达式。 *)

(** 正则表达式是用来描述字符串集合的一种简单语言，定义如下： *)

Inductive reg_exp (T : Type) : Type :=
  | EmptySet
  | EmptyStr
  | Char (t : T)
  | App (r1 r2 : reg_exp T)
  | Union (r1 r2 : reg_exp T)
  | Star (r : reg_exp T).

Arguments EmptySet {T}.
Arguments EmptyStr {T}.
Arguments Char {T} _.
Arguments App {T} _ _.
Arguments Union {T} _ _.
Arguments Star {T} _.

(** 请注意这个定义是_'多态的'_：[reg_exp T] 中的正则表达式描述了字符串，
    而其中的字符取自 [T]——也即，[T] 的元素构成的列表。

    （同一般的实践略有不同，我们不要求类型 [T] 是有限的。由此可形成一些不同的正则表达式
    理论，但对于我们在本章的目的而言并无不同。） *)

(** 我们通过以下规则来构建正则表达式和字符串，这些规则定义了正则表达式何时匹配一个字符串：

      - 表达式 [EmptySet] 不匹配任何字符串。

      - 表达式 [EmptyStr] 匹配空字符串 [[]].

      - 表达式 [Char x] 匹配单个字符构成的字符串 [[x]].

      - 如果 [re1] 匹配 [s1], 且 [re2] 匹配 [s2], 那么 [App re1 re2] 匹配 [s1 ++ s2].

      - 如果 [re1] 和 [re2] 中至少一个匹配 [s], 那么 [Union re1 re2] 匹配 [s].

      - 最后，如果我们写下某个字符串 [s] 作为一个字符串序列的连接
        [s = s_1 ++ ... ++ s_k]，且表达式 [re] 匹配其中每一个字符串 [s_i]，那么
        [Star re] 匹配 [s]。

        特别来说，此字符串序列可能为空，因此无论 [re] 是什么 [Star re]
        总是匹配空字符串 [[]]。*)

(** 容易把非形式化的定义翻译为使用 [Inductive] 的定义。我们用记法
    [s =~ re] 表示，通过把该记法用 [Reserved] “预留”在 [Inductive]
    定义之前，我们就能在定义中使用它！ *)

Reserved Notation "s =~ re" (at level 80).

Inductive exp_match {T} : list T -> reg_exp T -> Prop :=
  | MEmpty : [] =~ EmptyStr
  | MChar x : [x] =~ (Char x)
  | MApp s1 re1 s2 re2
             (H1 : s1 =~ re1)
             (H2 : s2 =~ re2)
           : (s1 ++ s2) =~ (App re1 re2)
  | MUnionL s1 re1 re2
                (H1 : s1 =~ re1)
              : s1 =~ (Union re1 re2)
  | MUnionR re1 s2 re2
                (H2 : s2 =~ re2)
              : s2 =~ (Union re1 re2)
  | MStar0 re : [] =~ (Star re)
  | MStarApp s1 s2 re
                 (H1 : s1 =~ re)
                 (H2 : s2 =~ (Star re))
               : (s1 ++ s2) =~ (Star re)
  where "s =~ re" := (exp_match s re).

Lemma quiz : forall T (s:list T), ~(s =~ EmptySet).
Proof. intros T s Hc. inversion Hc. Qed.
(** 出于可读性的考虑，在此我们也展示使用推断规则表示的定义。*)

(**

                          ----------------                    (MEmpty)
                           [] =~ EmptyStr

                          ---------------                      (MChar)
                           [x] =~ Char x

                       s1 =~ re1    s2 =~ re2
                      -------------------------                 (MApp)
                       s1 ++ s2 =~ App re1 re2

                              s1 =~ re1
                        ---------------------                (MUnionL)
                         s1 =~ Union re1 re2

                              s2 =~ re2
                        ---------------------                (MUnionR)
                         s2 =~ Union re1 re2

                          ---------------                     (MStar0)
                           [] =~ Star re

                      s1 =~ re    s2 =~ Star re
                     ---------------------------            (MStarApp)
                        s1 ++ s2 =~ Star re
*)

(** 请注意这些规则不_'完全'_等同于之前给出的非形式化定义。
    首先，我们并不需要一个规则来直接表述无字符串匹配 [EmptySet]；
    我们做的仅仅是不囊括任何可能导致有字符串被 [EmptySet] 所匹配的规则。
    （的确，归纳定义的语法并不_'允许'_我们表达类似的“否定规则”（negative rule））。

    其次，非形式化定义中的 [Union] 和 [Star] 各自对应了两个构造子：
    [MUnionL] / [MUnionR]，和 [MStar0] / [MStarApp]。这在逻辑上等价于
    原始的定义，但在 Coq 中这样更加方便，因为递归出现的 [exp_match]
    是作为构造子的直接参数给定的，这在对证据进行归纳时更简单。
    （练习 [exp_match_ex1] 和 [exp_match_ex2] 会要求你证明归纳定义中的构造子
    和从非形式化规则的表述中提炼的规则确实是等价的。）

    接下来我们对一些例子使用这些规则： *)

Example reg_exp_ex1 : [1] =~ Char 1.
Proof.
  apply MChar.
Qed.

Example reg_exp_ex2 : [1; 2] =~ App (Char 1) (Char 2).
Proof.
  apply (MApp [1] _ [2]).
  - apply MChar.
  - apply MChar.
Qed.

(** （请注意，后一个例子对字符串 [[1]] 和 [[2]] 直接应用了 [MApp]。
    由于目标的形式是 [[1; 2]] 而非 [[1] ++ [2]]，Coq 并不知道如何分解这个字符串。）

    使用 [inversion]，我们还可以证明某些字符串_'不'_匹配一个正则表达式： *)

Example reg_exp_ex3 : ~ ([1; 2] =~ Char 1).
Proof.
  intros H. inversion H.
Qed.

(** 我们可以定义一些辅助函数来简化正则表达式的书写。函数 [reg_exp_of_list]
    接受一个列表做参数，并构造一个正则表达式来精确地匹配这个列表：*)

Fixpoint reg_exp_of_list {T} (l : list T) :=
  match l with
  | [] => EmptyStr
  | x :: l' => App (Char x) (reg_exp_of_list l')
  end.

Example reg_exp_ex4 : [1; 2; 3] =~ reg_exp_of_list [1; 2; 3].
Proof.
  simpl. apply (MApp [1]).
  { apply MChar. }
  apply (MApp [2]).
  { apply MChar. }
  apply (MApp [3]).
  { apply MChar. }
  apply MEmpty.
Qed.

(** 我们还可以证明一些关于 [exp_match] 的性质。比如，下面的引理显示
    任意一个匹配 [re] 的字符串 [s] 也匹配 [Star re]。 *)

Lemma MStar1 :
  forall T s (re : reg_exp T) ,
    s =~ re ->
    s =~ Star re.
Proof.
  intros T s re H.
  rewrite <- (app_nil_r _ s).
  apply (MStarApp s [] re).
  - apply H.
  - apply MStar0.
Qed.

(** （请注意对 [app_nil_r] 的使用改变了目标，以此可匹配 [MStarApp] 所需要的形式。）*)

(** **** 练习：3 星, standard (exp_match_ex1) 

    下面的引理显示从形式化的归纳定义中可以得到本章开始的非形式化匹配规则。 *)

Lemma empty_is_empty : forall T (s : list T),
  ~ (s =~ EmptySet).
Proof.
  intros T s. unfold not. intros H. inversion H.
Qed. 

Lemma MUnion' : forall T (s : list T) (re1 re2 : reg_exp T),
  s =~ re1 \/ s =~ re2 ->
  s =~ Union re1 re2.
Proof.
  intros T s re1 re2 [H1 | H2].
  - apply MUnionL. apply H1.
  - apply MUnionR. apply H2.
Qed.   
(** 接下来的引理使用了 [Poly] 一章中出现的 [fold] 函数：
    如果 [ss : list (list T)] 表示一个字符串序列 [s1, ..., sn]，那么
    [fold app ss []] 是将所有字符串连接的结果。*)

Lemma MStar' : forall T (ss : list (list T)) (re : reg_exp T),
  (forall s, In s ss -> s =~ re) ->
  fold app ss [] =~ Star re.
Proof.
  intros T ss re H. induction ss as [|hs ts IHss].
  - simpl. apply MStar0.
  - simpl. apply MStarApp. 
    + apply H. simpl. left. reflexivity.
    + apply IHss. intros s H'. apply H. simpl.
      right. apply H'.
Qed.    
(** [] *)

(** **** 练习：4 星, standard, optional (reg_exp_of_list_spec) 

    请证明 [reg_exp_of_list] 满足以下规范： *)

Lemma reg_exp_of_list_spec : forall T (s1 s2 : list T),
  s1 =~ reg_exp_of_list s2 <-> s1 = s2.
Proof.
  intros T s1 s2. split.
  - generalize dependent s1. induction s2 as [| h2 t2 IHs2].
    + intros s1 H. simpl in H. inversion H. reflexivity.
    + intros s1 H. simpl in H. inversion H. inversion H3. simpl.
      f_equal. apply IHs2. apply H4.
  - generalize dependent s1. induction s2 as [| h2 t2 IHs2].
    + intros s1 H. rewrite H. simpl. apply MEmpty.
    + intros s1 H. rewrite H. simpl. 
      replace (h2::t2) with ([h2]++t2).
      apply MApp.
      * apply MChar.
      * apply IHs2. reflexivity.
      * simpl. reflexivity.
Qed.
(** [] *)

(** 由于 [exp_match] 以递归方式定义，我们可能会发现
    关于正则表达式的证明常常需要对证据进行归纳。*)

(** 比如，假设我们想要证明以下显然的结果：如果正则表达式 [re] 匹配某个字符串 [s]，
    那么 [s] 中的所有元素必在 [re] 中某处以字符字面量的形式出现。

    为了表达这个定理，我们首先定义函数 [re_chars] 来列举一个正则表达式中出现的
    所有字符：*)

Fixpoint re_chars {T} (re : reg_exp T) : list T :=
  match re with
  | EmptySet => []
  | EmptyStr => []
  | Char x => [x]
  | App re1 re2 => re_chars re1 ++ re_chars re2
  | Union re1 re2 => re_chars re1 ++ re_chars re2
  | Star re => re_chars re
  end.

(** 接下来我们这样陈述此定理： *)

Theorem in_re_match : forall T (s : list T) (re : reg_exp T) (x : T),
  s =~ re ->
  In x s ->
  In x (re_chars re).
Proof.
  intros T s re x Hmatch Hin.
  induction Hmatch
    as [| x'
        | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
        | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
        | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2].
  (* 课上已完成 *)
  - (* MEmpty *)
    simpl in Hin. destruct Hin.
  - (* MChar *)
    simpl. simpl in Hin.
    apply Hin.
  - (* MApp *)
    simpl.

(** Something interesting happens in the [MApp] case.  We obtain
    _two_ induction hypotheses: One that applies when [x] occurs in
    [s1] (which matches [re1]), and a second one that applies when [x]
    occurs in [s2] (which matches [re2]). *)

    simpl. rewrite In_app_iff in *.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      left. apply (IH1 Hin).
    + (* In x s2 *)
      right. apply (IH2 Hin).
  - (* MUnionL *)
    simpl. rewrite In_app_iff.
    left. apply (IH Hin).
  - (* MUnionR *)
    simpl. rewrite In_app_iff.
    right. apply (IH Hin).
  - (* MStar0 *)
    destruct Hin.
  - (* MStarApp *)
    simpl.

(** 我们再次得到了两个归纳假设，它们表明了为什么我们需要对 [exp_match]
    的证据而非 [re] 进行归纳：对后者的归纳仅仅提供匹配 [re]
    的字符串的归纳假设，却无法允许我们对 [In x s2] 分类进行推理。 *)

    rewrite In_app_iff in Hin.
    destruct Hin as [Hin | Hin].
    + (* In x s1 *)
      apply (IH1 Hin).
    + (* In x s2 *)
      apply (IH2 Hin).
Qed.

(** **** 练习：4 星, standard (re_not_empty) 

    请编写一个递归函数 [re_not_empty] 用来测试某个正则表达式是否会匹配一些字符串。
    并证明你的函数是正确的。*)
Search (bool).
Fixpoint re_not_empty {T : Type} (re : reg_exp T) : bool
  := match re with
    | EmptySet => false
    | EmptyStr => true
    | Char x => true
    | App re1 re2 => re_not_empty re1 && re_not_empty re2
    | Union re1 re2 => re_not_empty re1 || re_not_empty re2
    | Star re => true
    end.

Lemma re_not_empty_correct : forall T (re : reg_exp T),
  (exists s, s =~ re) <-> re_not_empty re = true.
Proof.
  intros T re. split.
  - intros [s H]. induction H.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. apply andb_true_iff. split. apply IHexp_match1. apply IHexp_match2.
    + simpl. apply orb_true_iff. left. apply IHexp_match.
    + simpl. apply orb_true_iff. right. apply IHexp_match.
    + simpl. reflexivity.
    + simpl. reflexivity.
  - intros H. induction re.
    + inversion H.
    + exists []. apply MEmpty.
    + exists [t]. apply MChar.
    + simpl in H. rewrite andb_true_iff in H. destruct H as [H1 H2].
      destruct IHre1 as [s1 H1']. apply H1.
      destruct IHre2 as [s2 H2']. apply H2.
      exists (s1++s2). apply MApp. apply H1'. apply H2'.
    + simpl in H. rewrite orb_true_iff in H. destruct H as [H1 | H2].
      * destruct IHre1 as [s1 H1']. apply H1. exists s1.
        apply MUnionL. apply H1'.
      * destruct IHre2 as [s2 H2']. apply H2. exists s2.
        apply MUnionR. apply H2'.
    + exists []. apply MStar0.
Qed.
(** [] *)

(* ================================================================= *)
(** ** [remember] 策略 *)

(** [induction] 策略让人困惑的一个特点是它会接受任意一个项并尝试归纳，
    即使这个项不够一般（general）。其副作用是会丢失掉一些信息（类似没有 [eqn:]
    从句的 [destruct]），并且使你无法完成证明。比如： *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.

(** 仅仅对 [H1] 反演并不会对处理含有递归的分类有太多帮助。（尝试一下！）
    因此我们需要对证据进行归纳！下面是一个朴素的尝试：*)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(** 现在，尽管我们得到了七个分类（正由我们从 [exp_match] 的定义中期待的那样），
    但 [H1] 还是丢失了一个非常重要的信息：[s1] 事实上匹配了某种形式的 [Star re]。
    这意味着对于_'全部'_的七个构造子分类我们都需要给出证明，尽管除了其中两个（[MStar0]
    和 [MStarApp]）之外，剩下的五个构造子分类是和前提矛盾的。
    我们仍然可以在一些构造子上继续证明，比如 [MEmpty]…… *)

  - (* MEmpty *)
    simpl. intros s2 H. apply H.

(** ……但有一些分类我们却卡住了。比如，对于 [MChar] 我们需要证明

    s2 =~ Char x' -> x' :: s2 =~ Char x',

    这显然是不可能完成的。 *)

  - (* MChar. *) intros s2 H. simpl. (* 卡住了…… *)
Abort.

(** 问题是，只有当 [Prop] 的假设是完全一般的时候，对其使用 [induction] 的才会起作用，
    也即，我们需要其所有的参数都是变量，而非更复杂的表达式，比如 [Star re]。

    （由此，对证据使用 [induction] 的行为更像是没有 [eqn:] 的 [destruct]
    而非 [inversion]。）

    解决此问题的一种直接的方式是“手动推广”这个有问题的表达式，
    即为此引理添加一个显式的等式： *)

Lemma star_app: forall T (s1 s2 : list T) (re re' : reg_exp T),
  re' = Star re ->
  s1 =~ re' ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.

(** 我们现在可以直接对证据进行归纳，因为第一个假设的参数已经足够一般，
    这意味着我们可以通过反演当前上下文中的 [re' = Star re] 来消解掉多数分类。

    这在 Coq 中是一种常用的技巧，因此 Coq 提供了策略来自动生成这种等式，
    并且我们也不必改写定理的陈述。*)

Abort.

(** 在 Coq 中调用 [remember e as x] 策略会（1）替换所有表达式 [e] 为变量 [x]，
    （2）在当前上下文中添加一个等式 [x = e]。我们可以这样使用 [remember]
    来证明上面的结果： *)

Lemma star_app: forall T (s1 s2 : list T) (re : reg_exp T),
  s1 =~ Star re ->
  s2 =~ Star re ->
  s1 ++ s2 =~ Star re.
Proof.
  intros T s1 s2 re H1.
  remember (Star re) as re'.

(** 我们现在有 [Heqre' : re' = Star re]. *)

  generalize dependent s2.
  induction H1
    as [|x'|s1 re1 s2' re2 Hmatch1 IH1 Hmatch2 IH2
        |s1 re1 re2 Hmatch IH|re1 s2' re2 Hmatch IH
        |re''|s1 s2' re'' Hmatch1 IH1 Hmatch2 IH2].

(**  [Heqre'] 与多数分类相互矛盾，因此我们可以直接结束这些分类。*)

  - (* MEmpty *)  discriminate.
  - (* MChar *)   discriminate.
  - (* MApp *)    discriminate.
  - (* MUnionL *) discriminate.
  - (* MUnionR *) discriminate.

(** 值得注意的分类是 [Star]。请注意 [MStarApp] 分类的归纳假设 [IH2]
    包含到一个额外的前提 [Star re'' = Star re]，这是由 [remember]
    所添加的等式所产生的。*)

  - (* MStar0 *)
    injection Heqre'. intros Heqre'' s H. apply H.

  - (* MStarApp *)
    injection Heqre'. intros H0.
    intros s2 H1. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hmatch1.
    + apply IH2.
      * rewrite H0. reflexivity.
      * apply H1.
Qed.

(** **** 练习：4 星, standard, optional (exp_match_ex2)  *)

(** 下面的引理 [MStar'']（以及它的逆，之前的练习题中的 [MStar']）显示
    [exp_match] 中 [Star] 的定义等价于前面给出的非形式化定义。*)

Lemma MStar'' : forall T (s : list T) (re : reg_exp T),
  s =~ Star re ->
  exists ss : list (list T),
    s = fold app ss []
    /\ forall s', In s' ss -> s' =~ re.
Proof.
  intros T s re H. remember (Star re) as re'. induction H.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - discriminate.
  - exists []. simpl. split.
    + reflexivity.
    + intros s' Hf. destruct Hf.
  - destruct IHexp_match2 as [ss' Hexp]. apply Heqre'.
    exists (s1::ss'). destruct Hexp as [Hexp1 Hexp2]. split.
    + assert (Hx: s1 ++ s2 =~ Star re0).
      * apply MStarApp. apply H. apply H0.
      * simpl. rewrite Hexp1. reflexivity.
    + simpl. intros s' [Hs1 | Hs2].
      * rewrite <- Hs1. injection Heqre'. intro Hre'. rewrite <- Hre'. 
        apply H.
      * apply Hexp2. apply Hs2.
Qed.  
(** [] *)

(** **** 练习：5 星, advanced (weak_pumping) 

    正则表达式中一个非常有趣的定理叫做_'泵引理（Pumping Lemma）'_，
    非形式化地来讲，它陈述了任意某个足够长的字符串 [s] 若匹配一个正则表达式 [re]，
    则可以被抽取（pumped）——将 [s] 的某个中间部分重复任意次产生的新字符串
    仍然匹配 [re]。
    （为了简单起见，我们考虑一个比自动机理论课上陈述的定理稍微弱一点的定理。）

    我们首先定义什么是“足够长”。由于 Coq 中使用的是构造性逻辑，我们事实上需要计算
    对于任何一个正则表达式 [re] 其最小的“可被抽取（pumpability）”长度。 *)

Module Pumping.

Fixpoint pumping_constant {T} (re : reg_exp T) : nat :=
  match re with
  | EmptySet => 1
  | EmptyStr => 1
  | Char _ => 2
  | App re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Union re1 re2 =>
      pumping_constant re1 + pumping_constant re2
  | Star r => pumping_constant r
  end.

(** 在证明后面的泵引理时，你会发现关于抽取常量的引理十分有用。 *)

Lemma pumping_constant_ge_1 :
  forall T (re : reg_exp T),
    pumping_constant re >= 1.
Proof.
  intros T re. induction re.
  - (* Emptyset *)
    apply le_n.
  - (* EmptyStr *)
    apply le_n.
  - (* Char *)
    apply le_S. apply le_n.
  - (* App *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Union *)
    simpl.
    apply le_trans with (n:=pumping_constant re1).
    apply IHre1. apply le_plus_l.
  - (* Star *)
    simpl. apply IHre.
Qed. 

Lemma pumping_constant_0_false :
  forall T (re : reg_exp T),
    pumping_constant re = 0 -> False.
Proof.
  intros T re H.
  assert (Hp1 : pumping_constant re >= 1).
  { apply pumping_constant_ge_1. }
  inversion Hp1 as [Hp1'| p Hp1' Hp1''].
  - rewrite H in Hp1'. discriminate Hp1'.
  - rewrite H in Hp1''. discriminate Hp1''.
Qed.

(** 接下来，定义辅助函数 [napp] 来重复（连接到它自己）一个字符串特定次数。*)

Fixpoint napp {T} (n : nat) (l : list T) : list T :=
  match n with
  | 0 => []
  | S n' => l ++ napp n' l
  end.

(** 这个辅助引理在你证明泵引理时也非常有用。 *)

Lemma napp_plus: forall T (n m : nat) (l : list T),
  napp (n + m) l = napp n l ++ napp m l.
Proof.
  intros T n m l.
  induction n as [|n IHn].
  - reflexivity.
  - simpl. rewrite IHn, app_assoc. reflexivity.
Qed.

Lemma napp_star :
  forall T m s1 s2 (re : reg_exp T),
    s1 =~ re -> s2 =~ Star re ->
    napp m s1 ++ s2 =~ Star re.
Proof.
  intros T m s1 s2 re Hs1 Hs2.
  induction m.
  - simpl. apply Hs2.
  - simpl. rewrite <- app_assoc.
    apply MStarApp.
    + apply Hs1.
    + apply IHm.
Qed.

Lemma emp_str_star :
  forall T (s: list T),
    s =~ Star EmptyStr -> s = [].
Proof.
  intros T s H. remember (Star EmptyStr) as res. 
  induction H.
  - reflexivity.
  - inversion Heqres.
  - inversion Heqres.
  - inversion Heqres.
  - inversion Heqres.
  - reflexivity.
  - injection Heqres as Heq'. rewrite Heq' in *.
    rewrite IHexp_match2. inversion H.
    reflexivity.
    reflexivity.
Qed.       

(** （弱化的）泵引理是说，如果 [s =~ re] 且 [s] 的长度最小是 [re] 的抽取常数（pumping constant），
    那么 [s] 可分割成三个子字符串 [s1 ++ s2 ++ s3]，其中 [s2] 可被重复任意次，
    其结果同 [s1] 和 [s3] 合并后仍然匹配 [re]。由于 [s2] 必须为非空字符串，
    这是一种（构造性的）方式来以我们想要的长度生成匹配 [re] 的字符串。 *)

Lemma weak_pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You are to fill in the proof. Several of the lemmas about
    [le] that were in an optional exercise earlier in this chapter
    may be useful. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
  - simpl. intros contra. inversion contra. inversion H0.
  - simpl. intros H1. rewrite app_length in H1. 
    apply add_le_cases in H1. destruct H1 as [H11 | H12].
    + destruct IH1 as [s1' [s2' [s3' [IH11 [IH12 IH13]]]]]. 
      apply H11. exists s1'. exists s2'. exists (s3'++s2).
      split.
      * rewrite IH11. 
        rewrite app_assoc. rewrite app_assoc. 
        rewrite app_assoc. reflexivity.
      * split. { apply IH12. }
        { 
          intros m. rewrite app_assoc. rewrite app_assoc.
          apply MApp. 
          { rewrite <- app_assoc. apply IH13. }
          { apply Hmatch2. }
        }
    + destruct IH2 as [s1' [s2' [s3' [IH11 [IH12 IH13]]]]]. 
      apply H12. exists (s1++s1'). exists s2'. exists s3'.
      split.
      * rewrite IH11. 
        rewrite app_assoc. rewrite app_assoc. 
        reflexivity.
      * split. { apply IH12. }
        { 
          intros m. rewrite <- app_assoc. apply MApp. 
          { apply Hmatch1. }
          { apply IH13. }
        }
  - simpl. intros H1. apply plus_le in H1. destruct H1 as [H11 H12].
    destruct IH as [s2' [s3' [s4' [IH11 [IH12 IH13]]]]].
    apply H11. exists s2'. exists s3'. exists s4'.
    split. apply IH11. split. apply IH12. 
    intros m. apply MUnionL. apply IH13.
  - simpl. intros H1. apply plus_le in H1. destruct H1 as [H11 H12].
    destruct IH as [s2' [s3' [s4' [IH11 [IH12 IH13]]]]].
    apply H12. exists s2'. exists s3'. exists s4'.
    split. apply IH11. split. apply IH12. 
    intros m. apply MUnionR. apply IH13.
  - simpl. intros contra. 
    inversion contra.
    apply pumping_constant_0_false in H0. destruct H0.
  - remember (Star re) as re'. induction Hmatch2.
    + inversion Heqre'. 
    + inversion Heqre'. 
    + inversion Heqre'. 
    + inversion Heqre'. 
    + inversion Heqre'.
    + injection Heqre' as Heqre''. intros H. 
      rewrite app_nil_r in *. 
      simpl in H. destruct IH1 as [s2' [s3' [s4' [IH11 [IH12 IH13]]]]]. 
      rewrite Heqre'' in *. apply H. 
      exists s2'. exists s3'. exists s4'.
      split. apply IH11. split. apply IH12.
      intros m. apply MStar1. rewrite Heqre''.
      apply IH13.
    + injection Heqre' as Heqre''. rewrite Heqre'' in *. 
      intros H.
      destruct s0 as [| h t] eqn:Hs0.
      * simpl. destruct IHHmatch2_2 as [s1' [s2' [s3' [IH11 [IH12 IH13]]]]].
        reflexivity. simpl in IH2. apply IH2.
        simpl in H. apply H.
        exists s1'. exists s2'. exists s3'.
        split. apply IH11. split. apply IH12.
        apply IH13.
      * exists s1. exists (h::t). exists s2.
        split. reflexivity. split.
        unfold not. intros contra. discriminate contra.
        intros m. apply MStarApp.
        apply Hmatch1. apply napp_star.
        apply Hmatch2_1. apply Hmatch2_2.
Qed.

(** [] *)

(** **** 练习：5 星, advanced, optional (pumping) 

    Now here is the usual version of the pumping lemma. In addition to
    requiring that [s2 <> []], it also requires that [length s1 +
    length s2 <= pumping_constant re]. *)
Lemma plus_le_plus: forall m n p q,
  m <= p /\ n <= q -> m + n <= p + q.
Proof.
  intros m n p q [H1 H2]. generalize dependent m. generalize dependent p.
  induction H2.
  - intros m p H1. induction n.
    + rewrite <- plus_n_O. rewrite <- plus_n_O. apply H1.
    + rewrite <- plus_n_Sm. rewrite <- plus_n_Sm. apply n_le_m__Sn_le_Sm.
      apply IHn.
  - intros p m' H1. rewrite <- plus_n_Sm. rewrite (plus_comm p m). 
    rewrite plus_n_Sm. rewrite (plus_comm m (S p)). apply IHle.
    apply le_S. apply H1.
Qed.

Lemma le_false_ge: forall m n,
  m <=? n = false -> n <= m.
Proof.
  intros m n H. 
  apply not_true_iff_false in H.
  unfold not in H.
  rewrite leb_iff in H.
  generalize dependent m.
  induction n.
  - intros m H. apply O_le_n.
  - intros m H. destruct m.
    + rewrite <- leb_iff in H. apply not_true_iff_false in H.
      discriminate H.
    + apply n_le_m__Sn_le_Sm. apply IHn.
      intros Hmn. apply H. apply n_le_m__Sn_le_Sm. apply Hmn.
Qed.           

Lemma pumping : forall T (re : reg_exp T) s,
  s =~ re ->
  pumping_constant re <= length s ->
  exists s1 s2 s3,
    s = s1 ++ s2 ++ s3 /\
    s2 <> [] /\
    length s1 + length s2 <= pumping_constant re /\
    forall m, s1 ++ napp m s2 ++ s3 =~ re.

(** You may want to copy your proof of weak_pumping below. *)
Proof.
  intros T re s Hmatch.
  induction Hmatch
    as [ | x | s1 re1 s2 re2 Hmatch1 IH1 Hmatch2 IH2
       | s1 re1 re2 Hmatch IH | re1 s2 re2 Hmatch IH
       | re | s1 s2 re Hmatch1 IH1 Hmatch2 IH2 ].
  - (* MEmpty *)
    simpl. intros contra. inversion contra.
    - simpl. intros contra. inversion contra. inversion H0.
    - simpl. intros H1. rewrite app_length in H1. 
      apply add_le_cases in H1 as H1'. destruct H1' as [H11 | H12].
      + destruct IH1 as [s1' [s2' [s3' [IH11 [IH12 [IH13 IH14]]]]]]. 
        apply H11. exists s1'. exists s2'. exists (s3'++s2).
        split.
        * rewrite IH11. 
          rewrite app_assoc. rewrite app_assoc. 
          rewrite app_assoc. reflexivity.
        * split. apply IH12.
          split. 
          apply (le_trans (length s1' + length s2') (pumping_constant re1) (pumping_constant re1 + pumping_constant re2)). 
          apply IH13. apply le_plus_l.
          { 
            intros m. rewrite app_assoc. rewrite app_assoc.
            apply MApp. 
            { rewrite <- app_assoc. apply IH14. }
            { apply Hmatch2. }
          }
      + destruct IH2 as [s1' [s2' [s3' [IH11 [IH12 [IH13 IH14]]]]]]. 
        apply H12. destruct (leb (pumping_constant re1) (length s1)) eqn:Eleb.
        * apply leb_iff in Eleb.
          destruct IH1 as [s1'' [s2'' [s3'' [IH11' [IH12'[IH13' IH14']]]]]].
          apply Eleb.
          exists s1''. exists s2''. exists (s3''++s2).
        split. rewrite IH11'.
        rewrite app_assoc. rewrite app_assoc. 
        rewrite app_assoc. reflexivity.
        split. apply IH12'.
        split. apply (le_trans (length s1'' + length s2'') (pumping_constant re1) (pumping_constant re1 + pumping_constant re2)). 
        apply IH13'. apply le_plus_l.
        { 
            intros m. rewrite app_assoc. rewrite app_assoc.
            apply MApp. 
            { rewrite <- app_assoc. apply IH14'. }
            { apply Hmatch2. }
          }
        * apply le_false_ge in Eleb. 
          exists (s1++s1'). exists s2'. exists s3'.
          split. rewrite IH11. 
          rewrite app_assoc. rewrite app_assoc. 
          reflexivity.
          split. { apply IH12. } split.
          simpl. rewrite app_length. rewrite <- plus_assoc.
          apply plus_le_plus. split.
          apply Eleb. apply IH13.
          { 
            intros m. rewrite <- app_assoc. apply MApp. 
            { apply Hmatch1. }
            { apply IH14. }
          }
    - simpl. intros H1. apply plus_le in H1. destruct H1 as [H11 H12].
      destruct IH as [s2' [s3' [s4' [IH11 [IH12 [IH13 IH14]]]]]].
      apply H11. exists s2'. exists s3'. exists s4'.
      split. apply IH11. split. apply IH12. 
      split. apply (le_trans (length s2' + length s3') (pumping_constant re1) (pumping_constant re1 + pumping_constant re2)).
      apply IH13. apply le_plus_l. 
      intros m. apply MUnionL. apply IH14.
    - simpl. intros H1. apply plus_le in H1. destruct H1 as [H11 H12].
      destruct IH as [s2' [s3' [s4' [IH11 [IH12 [IH13 IH14]]]]]].
      apply H12. exists s2'. exists s3'. exists s4'.
      split. apply IH11. split. apply IH12.
      split. apply (le_trans (length s2' + length s3') (pumping_constant re2) (pumping_constant re1 + pumping_constant re2)).
      apply IH13. rewrite plus_comm. apply le_plus_l.   
      intros m. apply MUnionR. apply IH14.
    - simpl. intros contra. 
      inversion contra.
      apply pumping_constant_0_false in H0. destruct H0.
    - intros H. destruct s1 as [|h t] eqn:Es1.
      + simpl in *. 
        destruct IH2 as [s1' [s2' [s3' [IH21 [IH22 [IH23 IH24]]]]]].
        * apply H. 
        * exists s1'. exists s2'. exists s3'.
          split. apply IH21.
          split. apply IH22.
          split. apply IH23.
          apply IH24.
      + destruct (leb (pumping_constant re) (length (h::t))) eqn:Elen.
        * apply leb_iff in Elen.
          destruct IH1 as [s1' [s2' [s3' [IH11 [IH12 [IH13 IH14]]]]]].
          apply Elen.
          exists s1'. exists s2'. exists (s3'++s2).
          split. rewrite IH11. rewrite <- app_assoc. rewrite <- app_assoc.
          reflexivity.
          split. apply IH12.
          split. apply IH13.
          intros m. rewrite app_assoc. rewrite app_assoc. 
          rewrite <- (app_assoc T s1' (napp m s2') s3').
          apply MStarApp.
          ** apply IH14.
          ** apply Hmatch2.
        * exists []. exists s1. exists s2.
          simpl in *. split. rewrite Es1. simpl. reflexivity.
          split. rewrite Es1. unfold not. intros contra.
          discriminate contra.
          split. apply le_false_ge in Elen. 
          rewrite Es1. simpl. apply Elen.
          intros m. apply napp_star. 
          rewrite Es1. apply Hmatch1.
          apply Hmatch2.
Qed.
  

End Pumping.
(** [] *)

(* ################################################################# *)
(** * 案例学习：改进互映 *)

(** 在 [Logic] 一章中，我们经常需要关联起对布尔值的计算和 [Prop]
    中的陈述，然而进行这样的关联往往会导致冗长的证明。请考虑以下定理的证明：*)

Theorem filter_not_empty_In : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (n =? m) eqn:H.
    + (* n =? m = true *)
      intros _. rewrite eqb_eq in H. rewrite H.
      left. reflexivity.
    + (* n =? m = false *)
      intros H'. right. apply IHl'. apply H'.
Qed.  

(** 在 [destruct] 后的第一个分支中，我们解构 [n =? m]
    后生成的等式显式地使用了 [eqb_eq] 引理，以此将假设
    [n =? m] 转换为假设 [n = m]；接着使用 [rewrite]
    策略和这个假设来完成此分支的证明。*)

(** 为了简化这样的证明，我们可定义一个归纳命题，用于对 [n =? m]
    产生更好的分类讨论原理。
    它不会生成类似 [(n =? m) = true]这样的等式，因为一般来说对证明并不直接有用，
    其生成的分类讨论原理正是我们所需要的假设: [n = m]。*)

Inductive reflect (P : Prop) : bool -> Prop :=
| ReflectT (H :   P) : reflect P true
| ReflectF (H : ~ P) : reflect P false.

(** 性质 [reflect] 接受两个参数：一个命题 [P] 和一个布尔值 [b]。
    直观地讲，它陈述了性质 [P] 在布尔值 [b] 中所_'映现'_（也即，等价）：
    换句话说，[P] 成立当且仅当 [b = true]。为了理解这一点，请注意定义，
    我们能够产生 [reflect P true] 的证据的唯一方式是证明 [P] 为真并使用
    [ReflectT] 构造子。如果我们反转这个陈述，意味着从 [reflect P true]
    的证明中抽取出 [P] 的证据也是可能的。与此类似，证明 [reflect P false]
    的唯一方式是合并 [~ P] 的证据和 [ReflectF] 构造子。

    形式化这种直觉并证明 [P <-> b = true] 和 [reflect P b]
    这两个表述确实等价是十分容易的。首先是从左到右的蕴含：*)

Theorem iff_reflect : forall P b, (P <-> b = true) -> reflect P b.
Proof.
  (* 课上已完成 *)
  intros P b H. destruct b.
  - apply ReflectT. rewrite H. reflexivity.
  - apply ReflectF. rewrite H. intros H'. discriminate.
Qed.

(** Now you prove the right-to-left implication: *)

(** **** 练习：2 星, standard, recommended (reflect_iff)  *)
Theorem reflect_iff : forall P b, reflect P b -> (P <-> b = true).
Proof.
  intros P b H. split.
  - intros H2. inversion H.
    + reflexivity.
    + exfalso. apply H0. apply H2.
  - intros H2. rewrite H2 in H. inversion H. apply H0.
Qed.    
(** [] *)

(** 使用 [reflect] 而非“当且仅当”连词的好处是，通过解构一个形如
    [reflect P b] 的假设或引理，我们可以对 [b]
    进行分类讨论，同时为两个分支（第一个子目标中的 [P]
    和第二个中的 [~ P]）生成适当的假设。 *)

Lemma eqbP : forall n m, reflect (n = m) (n =? m).
Proof.
  intros n m. apply iff_reflect. rewrite eqb_eq. reflexivity.
Qed.

(** [filter_not_empty_In] 的一种更流畅证明如下所示。请注意对 [destruct] 和 [rewrite]
    的使用是如何合并成一个 [destruct] 的使用。 *)

(** （为了更清晰地看到这点，使用 Coq 查看 [filter_not_empty_In]
    的两个证明，并观察在 [destruct] 的第一个分类开始时证明状态的区别。） *)

Theorem filter_not_empty_In' : forall n l,
  filter (fun x => n =? x) l <> [] ->
  In n l.
Proof.
  intros n l. induction l as [|m l' IHl'].
  - (* l = [] *)
    simpl. intros H. apply H. reflexivity.
  - (* l = m :: l' *)
    simpl. destruct (eqbP n m) as [H | H].
    + (* n = m *)
      intros _. rewrite H. left. reflexivity.
    + (* n <> m *)
      intros H'. right. apply IHl'. apply H'.
Qed.

(** **** 练习：3 星, standard, recommended (eqbP_practice) 

    使用上面的 [eqbP] 证明以下定理：*)

Fixpoint count n l :=
  match l with
  | [] => 0
  | m :: l' => (if n =? m then 1 else 0) + count n l'
  end.

Theorem eqbP_practice : forall n l,
  count n l = 0 -> ~(In n l).
Proof.
  intros n l. induction l as [| h' t' IHl].
  - simpl. intros H. unfold not. intros contra. apply contra.
  - simpl. destruct (eqbP n h').
    + simpl. intros contra. discriminate contra.
    + simpl. intros H'. unfold not. intros [H1 | H2].
      * rewrite H1 in H. apply H. reflexivity.
      * apply IHl. apply H'. apply H2.
Qed. 
(** [] *)

(** 这个小例子展示了互映证明可以怎样为我们提供一些便利。在大型的开发中，
    使用 [reflect] 往往更容易写出清晰和简短的证明脚本。我们将会在后面的章节
    和_'编程语言基础'_一卷中看到更多的例子。

    对 [reflect] 性质的使用已被 _'SSReflect'_ 推广开来，这是一个
    Coq 程序库，用于形式化一些数学上的重要结果，包括四色定理和法伊特－汤普森定理。
    SSReflect 的名字代表着 _'small-scale reflection'_，也即，普遍性地使用
    互映来简化与布尔值计算有关的证明。*)

(* ################################################################# *)
(** * 额外练习 *)

(** **** 练习：3 星, standard, recommended (nostutter_defn) 

    写出性质的归纳定义是本课程中你需要的重要技能。请尝试去独立解决以下的练习。

    列表连续地重复某元素称为 "百叶窗式" (stutter)。
    （此概念不同于不包含重复元素：[1;4;1] 虽然包含重复元素 [1]，
    但因其未连续出现，故不是百叶窗式列表）。
    [nostutter mylist] 表示 [mylist] 不是百叶窗式列表。
    请写出 [nostutter] 的归纳定义。 *)

Inductive nostutter {X:Type} : list X -> Prop :=
  | noshutter_nil : nostutter []
  | noshutter_sig e : nostutter [e]
  | noshutter_cons (h1 h2: X) t (H1: nostutter (h2::t)) (H2: h1 <> h2) : nostutter (h1::h2::t)
.

(** 请确保以下测试成功，但如果你觉得我们建议的证明（在注释中）并不有效，也可随意更改他们。
    若你的定义与我们的不同，也可能仍然是正确的，但在这种情况下可能需要不同的证明。
    （你会注意到建议的证明中使用了一些我们尚未讨论过的策略，这可以让证明适用于不同的 [nostutter]
    定义方式。你可以取消注释并直接使用他们，也可以用基础的策略证明这些例子。） *)

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor. apply eqb_neq; auto.
  apply eqb_neq; auto.
  apply eqb_neq; auto.
  apply eqb_neq; auto.
  apply eqb_neq; auto.
Qed.
(* 
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_2:  nostutter (@nil nat).
Proof.
  repeat constructor. 
Qed.
(* 
  Proof. repeat constructor; apply eqb_neq; auto.
  Qed.
*)

Example test_nostutter_3:  nostutter [5].
Proof.
  repeat constructor.
Qed.
(* 
  Proof. repeat constructor; apply eqb_false; auto. Qed.
*)

Example test_nostutter_4:      not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto.
Qed.
  
(* 
  Proof. intro.
  repeat match goal with
    h: nostutter _ |- _ => inversion h; clear h; subst
  end.
  contradiction; auto. Qed.
*)

(* 请勿修改下面这一行： *)
Definition manual_grade_for_nostutter : option (nat*string) := None.
(** [] *)

(** **** 练习：4 星, advanced (filter_challenge) 

    让我们证明在 [Poly] 一章中 [filter] 的定义匹配某个抽象的规范。
    可以这样非形式化地描述这个规范：

    列表 [l] 是一个 [l1] 和 [l2] 的“顺序合并”（in-order merge），如果它以
    [l1] 和 [l2] 中元素的顺序包含 [l1] 和 [l2] 中的所有元素，尽管可能是交替的。比如：

    [1;4;6;2;3]

    是

    [1;6;2]

    和

    [4;3].

    的顺序合并。

    现在，假设我们有集合 [X]，函数 [test: X->bool] 和一个类型为 [list X] 的列表
    [l]。接着接设如果 [l] 是 [l1] 和 [l2] 的顺序合并，且 [l1] 中的每个元素满足 [test]，
    而 [l2] 中没有元素满足 [test]，那么 [filter test l = l1]。

    请将这段规范翻译为 Coq 中的定理并证明它。（你首先需要定义合并两个列表的含义是什么。
    请使用归纳关系而非 [Fixpoint] 来完成。）*)

(* 请在此处解答 *)

Inductive in_order_merge {X:Type} : list X -> list X -> list X -> Prop :=
  | in_order_nil : in_order_merge [] [] []
  | in_order_left (h: X) t1 t2 t3 (H: in_order_merge t1 t2 t3) : in_order_merge (h::t1) (h::t2) t3
  | in_order_right (h: X) t1 t2 t3 (H: in_order_merge t1 t2 t3) : in_order_merge (h::t1) t2 (h::t3) 
.

Theorem in_order_merge_correct : forall (X: Type) (test: X -> bool) l l1 l2,
  in_order_merge l l1 l2 -> 
  All (fun x => test x = true) l1 -> All (fun x => test x = false) l2 ->
  filter test l = l1.
Proof.
  intros X test l l1 l2 H1. induction H1.
  - simpl. intros T1 T2. reflexivity.
  - simpl. intros [H21 H22] H3. rewrite H21.
    f_equal. apply IHin_order_merge.
    + apply H22.
    + apply H3.
  - simpl. intros H2 [H31 H32].
    rewrite H31. apply IHin_order_merge.
    + apply H2.
    + apply H32.
Qed. 

(* 请勿修改下面这一行： *)
Definition manual_grade_for_filter_challenge : option (nat*string) := None.
(** [] *)

(** **** 练习：5 星, advanced, optional (filter_challenge_2) 

    另一种刻画 [filter] 行为的方式是：在 [l] 的所有其元素满足 [test] 的子序列中，
    [filter test l] 是最长的那个。请形式化这个命题并证明它。*)

(* 请在此处解答

    [] *)

Inductive sublist {X:Type} : list X -> list X -> Prop :=
  | sublist_nil : sublist [] []
  | sublist_cons (h: X) t1 t2 (H: sublist t1 t2) : sublist t1 (h::t2)
  | sublist_cc (h: X) t1 t2 (H: sublist t1 t2) : sublist (h::t1) (h::t2)
.

Theorem filter_2 : forall (X: Type) (test: X -> bool) l l',
  sublist l' l -> All (fun x => test x = true) l' -> length l' <= length (filter test l).
Proof.
  intros X test l l' H1. induction H1.
  - simpl. intros T. apply le_n.
  - simpl. intros H. destruct (test h).
    + simpl. apply le_S. apply IHsublist. apply H.
    + apply IHsublist. apply H.
  - simpl. intros [H21 H22]. rewrite H21. simpl. 
    apply n_le_m__Sn_le_Sm. apply IHsublist.
    apply H22.
Qed.  

(** **** 练习：4 星, standard, optional (palindromes) 

    回文是倒序排列与正序排列相同的序列。

    - 在 [listX] 上定义一个归纳命题 [pal] 来表达回文的含义。
      （提示：你需要三个分类。定义应当基于列表的结构；仅仅使用一个构造子，例如

        c : forall l, l = rev l -> pal l

      看起来十分显而易见，但并不会很好的工作。)

    - 证明（[pal_app_rev]）

       forall l, pal (l ++ rev l).

    - 证明（[pal_rev] that）

       forall l, pal l -> l = rev l.
*)

(* 请在此处解答 *)

Inductive pal {X:Type} : list X -> Prop :=
  | pal_nil : pal []
  | pal_sig e : pal [e]
  | pal_cons (e: X) l (H: pal l): pal (e::l++[e])
.

Theorem pal_app_rev : forall (X: Type) (l: list X), pal (l ++ rev l).
Proof.
  intros X l. induction l as [| h t IHl].
  - simpl. apply pal_nil.
  - simpl. rewrite app_assoc. apply pal_cons. apply IHl.
Qed.

Theorem pal_rev : forall (X: Type) (l: list X), pal l -> l = rev l.
Proof.
  intros X l H. induction H.
  - simpl. reflexivity.
  - simpl. reflexivity.
  - simpl. rewrite rev_app_distr. simpl. rewrite <- IHpal. reflexivity.
Qed.  

(* 请勿修改下面这一行： *)
Definition manual_grade_for_pal_pal_app_rev_pal_rev : option (nat*string) := None.
(** [] *)

(** **** 练习：5 星, standard, optional (palindrome_converse) 

    由于缺乏证据，反方向的证明要困难许多。使用之前练习中定义的 [pal] 来证明

     forall l, l = rev l -> pal l.
*)

(* 请在此处解答

    [] *)

Inductive is_rev {X:Type} : list X -> list X -> Prop :=
  | rev_nil : is_rev [] []
  | rev_sig e : is_rev [e] [e]
  | rev_cons (e1 e2: X) l1 l2 (H: is_rev l1 l2): is_rev (e1::l1++[e2]) (e2::l2++[e1])
.

Lemma len_len : forall (X: Type) (l1 l2: list X), l1 = l2 -> length l1 = length l2.
Proof.
  intros X l1 l2 H.
  rewrite H. reflexivity.
Qed.

Lemma rev_to_rev : forall (X: Type) (l1 l2: list X), rev l1 = l2 -> l1 = rev l2.
Proof.
  intros X l1 l2 H. generalize dependent l1. 
  induction l2 as [| h t IHl].
  - intros l1 H. simpl. destruct l1 as [| h' t'] eqn:E'. 
    + reflexivity.
    + simpl in H. apply len_len in H. simpl in H. rewrite app_length in H.
      simpl in H. rewrite plus_comm in H. discriminate H. 
  - intros l1 H. rewrite <- H. rewrite rev_involutive. reflexivity.
Qed. 

Lemma rev_comm : forall (X: Type) (l1 l2: list X),  is_rev l1 l2 -> is_rev l2 l1.
Proof.
  intros X l1 l2 H. induction H.
  - apply rev_nil.
  - apply rev_sig.
  - apply rev_cons. apply IHis_rev. 
Qed.

Lemma rev_first : forall (X: Type) (l1 l2: list X) e,  is_rev l1 l2 -> is_rev (e::l1) (l2++[e]).
Proof.
  intros X l1 l2 e H. 
  generalize dependent e. induction H.
    + intros e. simpl. apply rev_sig.
    + intros e0. simpl. apply (rev_cons e0 e [] []). apply rev_nil.
    + intros e0. simpl. apply (rev_cons e0 e2 (e1::l1)(l2++[e1])).
    apply IHis_rev.
Qed.

Lemma rev_second : forall (X: Type) (l1 l2: list X) e,  is_rev (e::l1) (l2++[e]) -> is_rev l1 l2.
Proof.
  intros X l1 l2. generalize dependent l1. induction l2 as [| h t IHl]. 
  - intros l1 e H. simpl in H. inversion H.
    + apply rev_nil.
    + apply len_len in H4. rewrite app_length in H4. simpl in H4.
      rewrite plus_comm in H4. discriminate H4.
  - intros l1 e H. simpl in H. destruct (rev l1) as [| h' t'] eqn:El.
    + inversion H.
      * apply len_len in H4. rewrite app_length in H4. simpl in H4.
        rewrite plus_comm in H4. discriminate H4.
      * apply rev_to_rev in El. simpl in El. rewrite El in H2.
        apply len_len in H2. rewrite app_length in H2. simpl in H2.
        rewrite plus_comm in H2. discriminate H2.
    + apply rev_to_rev in El. simpl in El. rewrite El. 
      rewrite El in H. inversion H.
      * apply len_len in H2. rewrite app_length in H2. simpl in H2.
        rewrite plus_comm in H2. discriminate H2.
      * apply rev_comm. apply rev_first. apply rev_comm. 
        apply (IHl l0 e). rewrite <- H4. apply rev_first. apply H1.  
Qed.

Theorem rev_iff : forall (X: Type) (l1 l2: list X), l1 = rev l2 <-> is_rev l1 l2.
Proof.
  intros X l1 l2. split.
  - generalize dependent l1. induction l2 as [| h t IHl].
    + intros l1 H. simpl in H. rewrite H. apply rev_nil.
    + intros l1 H. destruct (rev l1) as [| h' t'] eqn:Et.
      * symmetry in H. apply rev_to_rev in H. rewrite Et in H. 
        simpl in H. discriminate H. 
      * apply rev_to_rev in Et. rewrite Et. simpl. rewrite Et in H.
        apply rev_to_rev in H. rewrite rev_involutive in H.
        injection H as H1 H2. rewrite H1. rewrite H2.
        destruct (rev t) as [| h'' t''] eqn:Et'.
        ** simpl. apply rev_to_rev in Et'. simpl in Et'.
           rewrite Et'. apply rev_sig.
        ** simpl. apply rev_to_rev in Et'. simpl in Et'.
           rewrite Et'. apply rev_cons. 
           apply (rev_second X t'' (rev t'') h'').
           rewrite <- Et'. apply IHl. reflexivity.
  - intros H. induction H.
    + simpl. reflexivity.
    + simpl. reflexivity.
    + simpl. rewrite rev_app_distr. simpl. rewrite IHis_rev.
      reflexivity. 
Qed.

Lemma rev_n : forall (X: Type) (l1 l2: list X) , l1 = l2 -> rev l1 = rev l2.
Proof.
  intros X l1 l2 H. rewrite H. reflexivity.
Qed.

Theorem palindrome_converse : forall (X: Type) (l: list X), l = rev l -> pal l.
Proof.
  intros X l H. apply rev_iff in H.
  remember H as H'. clear HeqH'.
  induction H.
  - apply pal_nil.
  - apply pal_sig.
  - inversion H'.
    + apply len_len in H2. rewrite app_length in H2.
      simpl in H2. rewrite plus_comm in H2. discriminate H2.
    + apply pal_cons. rewrite H3 in H2. apply rev_n in H2.
      rewrite rev_app_distr in H2. rewrite rev_app_distr in H2.
      simpl in H2. injection H2 as H21 H22. apply rev_n in H4. 
      rewrite rev_app_distr in H4. rewrite rev_app_distr in H4.
      simpl in H4. injection H4 as H4'.
      apply rev_n in H22. apply rev_n in H4'.
      rewrite rev_involutive in *. rewrite rev_involutive in *.
      rewrite H4'. rewrite H22. apply IHis_rev.
      rewrite H22 in H1. rewrite H4' in H1. rewrite H22 in H1.
      apply H1.
Qed. 

     
    
    
(** **** 练习：4 星, advanced, optional (NoDup) 

    请回忆一下 [Logic] 章节中性质 [In] 的定义，其断言值 [x] 在列表 [l] 中至少出现一次：*)

(* Fixpoint In (A : Type) (x : A) (l : list A) : Prop :=
   match l with
   | [] => False
   | x' :: l' => x' = x \/ In A x l'
   end *)

(** 你的第一个任务是使用 [In] 来定义命题 [disjoint X l1 l2]：仅当列表 [l1]
    和 [l2]（元素的类型为 [X]）不含有相同的元素时其可被证明。*)

(* 请在此处解答 *)

Inductive disjoint {X: Type} : list X -> list X -> Prop :=
  | disjoint_nil : disjoint [] []
  | disjoint_left e (t1 t2: list X) (H1: disjoint t1 t2) (H2: ~(In e t2)) : disjoint (e::t1) t2
  | disjoint_right e (t1 t2: list X) (H1: disjoint t1 t2) (H2: ~(In e t1)) : disjoint t1 (e::t2)
  .

(** 接下来，使用 [In]　定义归纳命题 [NoDup X l]，其可被证明仅当列表 [l]
    （元素类型为 [X]）的每个元素都不相同。比如，[NoDup nat [1;2;3;4]]
    和 [NoDup bool []] 是可被证明的，然而 [NoDup nat [1;2;1]]
    和 [NoDup bool [true;true]] 是不行的。*)

(* 请在此处解答 *)

Inductive NoDup {X: Type} : list X -> Prop :=
  | NoDup_nil : NoDup []
  | NoDup_el h (t: list X) (H1: ~ (In h t)) (H2: NoDup t) : NoDup (h::t)
. 

(** 最后，使用 [disjoint]，[NoDup] 和 [++]（列表连接）陈述并证明一个或多个有趣的定理。 *)

(* 请在此处解答 *)

Theorem nodup_mid : forall (X: Type) (l1 l2: list X),
  NoDup (l1++l2) -> NoDup l1 /\ NoDup l2.
Proof.
  intros X l1. induction l1 as [| h t IHl1].
  - intros l2 H. simpl in *. split.
    + apply NoDup_nil.
    + apply H.
  - intros l2 H. simpl in *. inversion H.
    split.
    + apply NoDup_el. rewrite In_app_iff in H0.
      unfold not. intros contra. apply H0. left. apply contra.
      apply (IHl1 l2). apply H3.
    + apply (IHl1 l2). apply H3.
Qed.

Lemma head_nodup : forall (X: Type) (l: list X) e,
  NoDup(e::l) -> ~ In e l.
Proof.
  intros X l e H. inversion H. apply H0.
Qed.

Lemma head_disjoint : forall (X: Type) (l1 l2: list X) e,
  disjoint (e::l1) l2 -> disjoint l1 l2.
Proof.
  intros X l1 l2 e H. remember (e::l1) as l'.
  induction H.
  - discriminate Heql'.
  - injection Heql' as H1' H2'. rewrite <- H2'. apply H.
  - apply disjoint_right.
    + apply IHdisjoint. apply Heql'.
    + rewrite Heql' in H2. simpl in H2.
      intros contra. apply H2. right. apply contra.
Qed.    

Lemma disjoint_nil_any : forall (X: Type) (l: list X),
  disjoint [] l.
Proof.
  intros X l. induction l as [| h t IHl].
  - apply disjoint_nil.
  - apply disjoint_right. apply IHl. simpl. intros contra. destruct contra.
Qed.

Theorem disjoint_app_nodup : forall (X: Type) (l1 l2: list X),
  NoDup (l1++l2) -> disjoint l1 l2.
Proof.
  intros X l1 l2 H. induction l1 as [| h t IHl1].
    + simpl in *. apply disjoint_nil_any.
    + simpl in *. apply disjoint_left.
      apply IHl1. apply (nodup_mid X [h] (t++l2)) in H.
      destruct H as [H1 H2]. apply H2.
      apply head_nodup in H. rewrite In_app_iff in H.
      intros c. apply H. right. apply c.
Qed. 
              
(* 请勿修改下面这一行： *)
Definition manual_grade_for_NoDup_disjoint_etc : option (nat*string) := None.
(** [] *)

(** **** 练习：4 星, advanced, optional (pigeonhole_principle) 

    _鸽笼原理（Pigeonhole Principle）'_是一个关于计数的基本事实：
    将超过 [n] 个物体放进 [n] 个鸽笼，则必有鸽笼包含至少两个物体。
    与此前诸多情形相似，这一数学事实看似乏味，但其证明手段并不平凡，
    如下所述： *)

(** 首先容易证明一个有用的引理。 *)

Lemma in_split : forall (X:Type) (x:X) (l:list X),
  In x l ->
  exists l1 l2, l = l1 ++ x :: l2.
Proof.
  intros X x l H. induction l as [| h t IHl].
  - destruct H.
  - destruct H.
    + exists []. exists t. simpl. rewrite H. reflexivity.
    + destruct IHl as [l1 [l2]]. apply H.
      exists (h::l1). exists l2. simpl. rewrite H0. reflexivity.
Qed.  

(** 现在请定一个性质 [repeats]，使 [repeats X l] 断言 [l]
    包含至少一个（类型为 [X] 的）重复的元素。*)

Inductive repeats {X:Type} : list X -> Prop :=
  | repeat_n : repeats []
  | repeat_s (e: X) (l: list X) (H: repeats l) : repeats (e::l)
  | repeat_e (e: X) (l: list X) (H: In e l) : repeats (e::l)
.

(** 现在，我们这样来形式化鸽笼原理。假设列表 [l2] 表示鸽笼标签的列表，列表 [l1]
    表示标签被指定给一个列表里的元素。如果元素的个数多于标签的个数，那么至少有两个
    元素被指定了同一个标签——也即，列表 [l1] 含有重复元素。

    如果使用 [excluded_middule] 假设并展示 [In] 是可判定的（decidable），
    即 [forall x l, (In x l) \/ ~ (In x l)]，那么这个证明会容易很多。
    然而，若_'不'_假设 [In] 的可判定性也同样可以证明它；在这样的情况下便不必使用
    [excluded_middle] 假设。 *)

Theorem pigeonhole_principle: forall (X:Type) (l1  l2:list X),
   excluded_middle ->
   (forall x, In x l1 -> In x l2) ->
   length l2 < length l1 ->
   repeats l1.
Proof.
   intros X l1. induction l1 as [|x l1' IHl1'].
   - intros l2 exm Hf Hl. simpl in Hl. inversion Hl.
   - intros l2 exm Hf Hl. destruct (exm (In x l1')). 
    + apply repeat_e. apply H.
    + apply repeat_s. simpl in Hf. remember Hf as Hf'. 
      clear HeqHf'.
      apply (in_split X x) in Hf.
      destruct Hf as [l1 [l3 Hf]]. rewrite Hf in Hl.
      rewrite app_length in Hl. simpl in Hl. rewrite <- plus_n_Sm in Hl.
      rewrite <- app_length in Hl. apply (IHl1' (l1++l3)).
      * apply exm.
      * intros x0 H'. rewrite Hf in Hf'.
        remember (Hf' x0) as Hfx0.
        clear HeqHfx0.
        rewrite In_app_iff in Hfx0.
        destruct Hfx0.
        ** right. apply H'.
        ** apply In_app_iff. left. apply H0.
        ** simpl in H0. destruct H0.
          *** rewrite <- H0 in H'. exfalso. apply H. apply H'.
          *** apply In_app_iff. right. apply H0.
      * unfold lt. unfold lt in Hl. apply Sn_le_Sm__n_le_m in Hl.
        apply Hl.
      * left. reflexivity.
Qed.
  

(* GRADE_MANUAL 1.5: check_repeats

    [] *)

(* ================================================================= *)
(** ** 扩展练习：经验证的正则表达式匹配器 *)

(** 我们现在已经定义了正则表达式的匹配关系和多态列表。我们可以使用这些定义来手动地证明
    给定的正则表达式是否匹配某个字符串，但这并不是一个可以自动地判断是否匹配的程序。

    有理由期待，用于构造匹配关系证据的归纳规则可以被翻译为一个递归函数，
    其在正则表达式上的递归对应于这种关系。然而，定义这样的函数并没有那么直接，
    由于给定的正则表达式会被 Coq 识别为递归变量，作为结果，Coq 并不会接受这个函数，
    即使它总是停机。

    重度优化的匹配器会将正则表达式翻译为一个状态机，并决定状态机是否接受
    某个字符串。然而，正则表达式匹配也可以通过一个算法来实现，其仅仅操作字符串和
    正则表达式，无需定义和维护额外的数据类型，例如状态机。我们将会实现这样的算法，
    并验证其值与匹配关系是互映的。 *)

(** 我们将要实现的正则表达式匹配器会匹配由 ASCII 字符构成的列表：*)
Require Import Stdlib.Strings.Ascii.

Definition string := list ascii.

(** Coq 标准库中包含了一个不同的 ASCII 字符串的归纳定义。然而，为了应用
    之前定义的匹配关系，我们在此使用刚刚给出的 ASCII 字符列表作为定义。

    我们也可以定义工作在多态列表上的正则表达式匹配器，而非特定于 ASCII 字符列表。
    我们将要实现的匹配算法需要知道如何对列表中的元素判断相等，因此需要给定一个
    相等关系测试函数。一般化我们给出的定义、定理和证明有一点枯燥，但是可行的。 *)

(** 正则表达式匹配器的正确性证明会由匹配函数的性质和 [match] 关系的性质组成，
    [match] 关系并不依赖匹配函数。我们将会首先证明后一类性质。他们中的多数
    将会是很直接的证明，已经被直接给出；少部分关键的引理会留给你来证明。 *)

(** 每个可被证明的 [Prop] 等价于 [True]。 *)
Lemma provable_equiv_true : forall (P : Prop), P -> (P <-> True).
Proof.
  intros.
  split.
  - intros. constructor.
  - intros _. apply H.
Qed.

(** 其逆可被证明的 [Prop] 等价于 [False]。 *)
Lemma not_equiv_false : forall (P : Prop), ~P -> (P <-> False).
Proof.
  intros.
  split.
  - apply H.
  - intros. destruct H0.
Qed.

(** [EmptySet] 不匹配字符串。 *)
Lemma null_matches_none : forall (s : string), (s =~ EmptySet) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [EmptyStr] 仅匹配空字符串。 *)
Lemma empty_matches_eps : forall (s : string), s =~ EmptyStr <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MEmpty.
Qed.

(** [EmptyStr] 不匹配非空字符串。 *)
Lemma empty_nomatch_ne : forall (a : ascii) s, (a :: s =~ EmptyStr) <-> False.
Proof.
  intros.
  apply not_equiv_false.
  unfold not. intros. inversion H.
Qed.

(** [Char a] 不匹配不以 [a] 字符开始的字符串。 *)
Lemma char_nomatch_char :
  forall (a b : ascii) s, b <> a -> (b :: s =~ Char a <-> False).
Proof.
  intros.
  apply not_equiv_false.
  unfold not.
  intros.
  apply H.
  inversion H0.
  reflexivity.
Qed.

(** 如果 [Char a] 匹配一个非空字符串，那么这个字符串的尾（tail）为空。 *)
Lemma char_eps_suffix : forall (a : ascii) s, a :: s =~ Char a <-> s = [ ].
Proof.
  split.
  - intros. inversion H. reflexivity.
  - intros. rewrite H. apply MChar.
Qed.

(** [App re0 re1] 匹配字符串 [s] 当且仅当 [s = s0 ++ s1]，其中 [s0]
    匹配 [re0] 且 [s1] 匹配 [re1]。 *)
Lemma app_exists : forall (s : string) re0 re1,
    s =~ App re0 re1 <->
    exists s0 s1, s = s0 ++ s1 /\ s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros.
  split.
  - intros. inversion H. exists s1, s2. split.
    * reflexivity.
    * split. apply H3. apply H4.
  - intros [ s0 [ s1 [ Happ [ Hmat0 Hmat1 ] ] ] ].
    rewrite Happ. apply (MApp s0 _ s1 _ Hmat0 Hmat1).
Qed.

(** **** 练习：3 星, standard, optional (app_ne) 

    [App re0 re1] 匹配 [a::s] 当且仅当 [re0] 匹配空字符串
    且 [a::s] 匹配 [re1] 或 [s=s0++s1]，其中 [a::s0] 匹配 [re0]
    且 [s1] 匹配 [re1]。

    尽管这个性质由纯粹的匹配关系构成，它是隐藏在匹配器的设计背后的一个重要观察。
    因此（1）花一些时间理解它，（2）证明它，并且（3）留心后面你会如何使用它。*)
Lemma app_ne : forall (a : ascii) s re0 re1,
    a :: s =~ (App re0 re1) <->
    ([ ] =~ re0 /\ a :: s =~ re1) \/
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re0 /\ s1 =~ re1.
Proof.
  intros a s re0 re1. split.
  - intros H. inversion H. destruct s1 eqn:Es1.
    + left. split. apply H3. simpl in *. apply H4.
    + right. simpl in H1. injection H1 as H1 H1'. exists l. exists s2.
      split. symmetry. apply H1'.
      split. rewrite <- H1. apply H3.
      apply H4.
  - intros [[H1 H2]|[s0 [s1 [H1 [H2 H3]]]]].
    + assert(Hn: []++a::s = a::s). simpl. reflexivity. 
      rewrite <- Hn.
      apply MApp. apply H1. apply H2.
    + rewrite H1. assert(Hn: a::s0++s1 = (a::s0)++s1). simpl. reflexivity. 
      rewrite Hn. apply MApp. apply H2. apply H3.
Qed. 
(** [] *)

(** [s] 匹配 [Union re0 re1] 当且仅当 [s] 匹配 [re0] 或 [s] 匹配 [re1]. *)
Lemma union_disj : forall (s : string) re0 re1,
    s =~ Union re0 re1 <-> s =~ re0 \/ s =~ re1.
Proof.
  intros. split.
  - intros. inversion H.
    + left. apply H2.
    + right. apply H1.
  - intros [ H | H ].
    + apply MUnionL. apply H.
    + apply MUnionR. apply H.
Qed.

(** **** 练习：3 星, standard, optional (star_ne) 

    [a::s] 匹配 [Star re] 当且仅当 [s = s0 ++ s1]，其中 [a::s0] 匹配
    [re] 且 [s1] 匹配 [Star re]。 同 [app_ne]一样，这个观察很重要，
    因此理解，证明并留意它。

    提示：你需要进行归纳。的确是有几个合理的候选 [Prop] 来进行归纳。
    但唯一其作用的方式是首先拆分 [iff] 为两个蕴含式，然后在 [a :: s =~ Star re]
    的证据上进行归纳来证明其中一个。另一个蕴含式可以无需使用归纳来证明。

    为了在正确的性质上归纳，你需要使用 [remember] 策略来重新表述 [a :: s =~ Star re]，
    使其成为一般变量上的 [Prop]。 *)

Lemma star_ne : forall (a : ascii) s re,
    a :: s =~ Star re <->
    exists s0 s1, s = s0 ++ s1 /\ a :: s0 =~ re /\ s1 =~ Star re.
Proof.
  intros a s re. split.
  - intros H. remember (a::s) as s'. remember (Star re) as re'.
    induction H.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqre'.
    + inversion Heqs'.
    + destruct s1 as [| h t] eqn:Es1.
      * simpl in *. apply IHexp_match2.
        apply Heqs'. apply Heqre'.
      * simpl in Heqs'. injection Heqs' as He Hq.
        injection Heqre' as Heqre.
        exists t. exists s2.
        split. symmetry. apply Hq.
        split. rewrite He in H. rewrite Heqre in H. apply H.
        apply H0.
  - intros [s0 [s1 [H1 [H2 H3]]]].
    rewrite H1. 
    assert(Hn: a::s0++s1 = (a::s0)++s1). simpl. reflexivity.
    rewrite Hn. apply MStarApp. apply H2. apply H3.
Qed.
        
(** [] *)

(** 我们的正则表达式匹配器定义包括两个不动点函数。第一个函数对给定的正则表达式 [re]
    进行求值，结果映射了 [re] 是否匹配空字符串。这个函数满足以下性质： *)
Definition refl_matches_eps m :=
  forall re : reg_exp ascii, reflect ([ ] =~ re) (m re).

(** **** 练习：2 星, standard, optional (match_eps) 

    完成 [match_eps] 的定义，其测试给定的正则表达式是否匹配空字符串： *)
Fixpoint match_eps (re: reg_exp ascii) : bool :=
  match re with
  | EmptySet => false
  | EmptyStr => true
  | Char _ => false
  | Union re1 re2 => (match_eps re1) || (match_eps re2)
  | App re1 re2 => (match_eps re1) && (match_eps re2) 
  | Star _ => true
  end.
(** [] *)

(** **** 练习：3 星, standard, optional (match_eps_refl) 

    现在，请证明 [match_eps] 确实测试了给定的正则表达式是否匹配空字符串。
    （提示：你会使用到互映引理 [ReflectT] 和 [ReflectF]。） *)
Lemma match_eps_refl : refl_matches_eps match_eps.
Proof.
  unfold refl_matches_eps. intros re. 
  induction re.
  - simpl. apply ReflectF. intros contra. inversion contra.
  - simpl. apply ReflectT. apply MEmpty.
  - simpl. apply ReflectF. intros contra. inversion contra.
  - simpl.  apply iff_reflect. split.
    + intros H. inversion H. destruct s1 eqn:Es1.
      * simpl in *. rewrite H1 in H4.
        apply andb_true_iff. split.
        destruct IHre1. reflexivity.
        destruct H5. apply H3.
        destruct IHre2. reflexivity.
        destruct H5. apply H4.
      * simpl in H1. discriminate H1.
    + intros H. apply andb_true_iff in H. destruct H as [H1 H2].
      rewrite <- (app_nil_r ascii []). apply MApp.
      destruct IHre1. apply H. discriminate H1.
      destruct IHre2. apply H. discriminate H2.
  - simpl. apply iff_reflect. split.
    + intros H. apply orb_true_iff. inversion H.
      * left. destruct IHre1. reflexivity. destruct H4. apply H2.
      * right. destruct IHre2. reflexivity. destruct H4. apply H1.
    + intros H. apply orb_true_iff in H. destruct H as [H1 | H2].
      * apply MUnionL. destruct IHre1. apply H. discriminate H1.
      * apply MUnionR. destruct IHre2. apply H. discriminate H2.
  - simpl. apply ReflectT. apply MStar0.
Qed.    
(** [] *)

(** 我们将会定义其他函数也使用到 [match_eps]。然而，这些函数的证明中你唯一会用到的
    [match_eps] 的性质是 [match_eps_refl]。*)

(** 我们匹配器所进行的关键操作是迭代地构造一个正则表达式生成式的序列。
    对于字符 [a] 和正则表达式 [re]，[re] 在 [a] 上的生成式是一个正则表达式，
    其匹配所有匹配 [re] 且以 [a] 开始的字符串的后缀。也即，[re']
    是 [re] 在 [a] 上的一个生成式如果他们满足以下关系：*)

Definition is_der re (a : ascii) re' :=
  forall s, a :: s =~ re <-> s =~ re'.

(** 函数 [d] 生成字符串如果对于给定的字符 [a] 和正则表达式 [re]，
    它求值为 [re] 在 [a] 上的生成式。也即，[d] 满足以下关系： *)
Definition derives d := forall a re, is_der re a (d a re).

(** **** 练习：3 星, standard, optional (derive) 

    请定义 [derive] 使其生成字符串。一个自然的实现是在某些分类使用
    [match_eps] 来判断正则表达式是否匹配空字符串。 *)

Fixpoint derive (a : ascii) (re : reg_exp ascii) : reg_exp ascii :=
  match re with
  | EmptySet => EmptySet
  | EmptyStr => EmptySet
  | Char x => if (nat_of_ascii x =? nat_of_ascii a) then EmptyStr else EmptySet 
  | App re1 re2 => if (match_eps re1) then 
                    Union (App (derive a re1) re2) (derive a re2)
                   else App (derive a re1) re2
  | Union re1 re2 => Union (derive a re1) (derive a re2)
  | Star re => App (derive a re) (Star re) 
  end.
(** [] *)

(** [derive] 函数应当通过以下测试。每个测试都在将被匹配器所求值的表达式和
    最终被匹配器返回的结果之间确立一种相等关系。
    每个测试也被添加了它所反映的匹配事实的注解。*)
Example c := ascii_of_nat 99.
Example d := ascii_of_nat 100.

(** "c" =~ EmptySet: *)
Example test_der0 : match_eps (derive c (EmptySet)) = false.
Proof.
  simpl. reflexivity.
Qed.

(** "c" =~ Char c: *)
Example test_der1 : match_eps (derive c (Char c)) = true.
Proof.
  simpl. reflexivity.
Qed.

(** "c" =~ Char d: *)
Example test_der2 : match_eps (derive c (Char d)) = false.
Proof.
  simpl. reflexivity.
Qed.

(** "c" =~ App (Char c) EmptyStr: *)
Example test_der3 : match_eps (derive c (App (Char c) EmptyStr)) = true.
Proof.
  simpl. reflexivity.
Qed.

(** "c" =~ App EmptyStr (Char c): *)
Example test_der4 : match_eps (derive c (App EmptyStr (Char c))) = true.
Proof.
  simpl. reflexivity.
Qed.

(** "c" =~ Star c: *)
Example test_der5 : match_eps (derive c (Star (Char c))) = true.
Proof.
  simpl. reflexivity.
Qed.

(** "cd" =~ App (Char c) (Char d): *)
Example test_der6 :
  match_eps (derive d (derive c (App (Char c) (Char d)))) = true.
Proof.
  simpl. reflexivity.
Qed.

(** "cd" =~ App (Char d) (Char c): *)
Example test_der7 :
  match_eps (derive d (derive c (App (Char d) (Char c)))) = false.
Proof.
  simpl. reflexivity.
Qed.

(** **** 练习：4 星, standard, optional (derive_corr) 

    请证明 [derive] 确实总是会生成字符串。

    提示：一种证明方法是对 [re] 归纳，尽管你需要通过归纳和一般化合适的项来
    仔细选择要证明的性质。

    提示：如果你定义的 [derive] 对某个正则表达式 [re] 使用了 [match_eps]，
    那么可对 [re] 应用 [match_eps_refl]，接着对结果解构并生成
    分类，其中你可以假设 [re] 匹配或不匹配空字符串。

    提示：通过使用之前证明过的引理可以帮助一点你的工作。特别是，在证明归纳的
    许多分类时，通过之前的引理，你可以用一个复杂的正则表达式（比如，
    [s =~ Union re0 re1]）来重写命题，得到一个简单正则表达式上的命
    题构成的布尔表达式（比如，[s =~ re0 \/ s =~ re1]）。
    你可以使用 [intro] 和 [destruct] 来对这些命题进行推理。*)
Lemma derive_corr : derives derive.
Proof.
  unfold derives. intros a re.
  induction re.
  - simpl. unfold is_der. intros s. split.
    + intros H. inversion H.
    + intros H. inversion H.
  - simpl. unfold is_der. intros s. split.
    + intros H. inversion H.
    + intros H. inversion H.
  - simpl. unfold is_der. intros s. split.
    + intros H. inversion H.
      destruct (eqbP (nat_of_ascii t) (nat_of_ascii t)).
      * apply MEmpty.
      * destruct H0. reflexivity.
    + intros H. destruct (eqbP (nat_of_ascii t) (nat_of_ascii a)).
      * inversion H. 
        apply (f_equal nat ascii ascii_of_nat (nat_of_ascii t) (nat_of_ascii a)) in H0.
        rewrite ascii_nat_embedding in H0. rewrite ascii_nat_embedding in H0.
        rewrite H0. apply MChar.
      * inversion H.
  - simpl. unfold is_der. intros s. split.
    + intros H. apply app_ne in H. destruct (match_eps_refl re1).
      * destruct H as [[H11 H12]| [s0 [s1 [H21 [H22 H23]]]]].
        ** apply MUnionR. unfold is_der in IHre2. apply IHre2. apply H12.
        ** apply MUnionL. rewrite H21. apply MApp. apply IHre1. apply H22. apply H23.
      * destruct H as [[H11 H12]| [s0 [s1 [H21 [H22 H23]]]]].
        ** destruct H0. apply H11.
        ** apply app_exists. exists s0. exists s1.
          split. apply H21.
          split. apply IHre1. apply H22.
          apply H23.
    + intros H. apply app_ne. destruct (match_eps_refl re1).
      * inversion H.
        ** inversion H3. right. exists s0. exists s2.
           split. reflexivity.
           split. apply IHre1. apply H8. apply H9.
        ** left. split. apply H0. apply IHre2. apply H3.
      * inversion H.
        ** right. exists s1. exists s2.
           split. reflexivity.
           split. apply IHre1. apply H4. apply H5.
  - simpl. unfold is_der. intros s. split.
    + intros H. apply union_disj in H. destruct H as [H1|H2].
      * apply MUnionL. apply IHre1. apply H1.
      * apply MUnionR. apply IHre2. apply H2.
    + intros H. apply union_disj. inversion H.
      * left. apply IHre1. apply H2.
      * right. apply IHre2. apply H1.
  - simpl. unfold is_der. intros s. split.
    + intros H. apply star_ne in H. 
      destruct H as [s0 [s1 [H1 [H2 H3]]]].
      rewrite H1. apply MApp.
      * apply IHre. apply H2.
      * apply H3.
    + intros H. apply star_ne. inversion H.
      exists s1. exists s2.
      split. reflexivity.
      split. apply IHre. apply H3.
      apply H4.
Qed.  

(** [] *)

(** 我们将会使用 [derive] 来定义正则表达式匹配器。然而，在匹配器的性质的证明中你唯一会用到
    的 [derive] 的性质是 [derive_corr]。 *)

(** 函数 [m] 匹配正则表达式如果对给定的字符串 [s] 和正则表达式 [re]，
    它求值的结果映射了 [s] 是否被 [re] 匹配。也即，[m] 满足以下性质：*)
Definition matches_regex m : Prop :=
  forall (s : string) re, reflect (s =~ re) (m s re).

(** **** 练习：2 星, standard, optional (regex_match) 

    完成 [regex_match] 的定义，使其可以匹配正则表达式。*)
Fixpoint regex_match (s : string) (re : reg_exp ascii) : bool :=
  match s with
  | [] => match_eps re
  | h::t => regex_match t (derive h re)
  end. 
(** [] *)

(** **** 练习：3 星, standard, optional (regex_refl) 

    最后，证明 [regex_match] 确实可以匹配正则表达式。

    提示：如果你定义的 [regex_match] 对正则表达式 [re] 使用了 [match_eps]，
    那么可对 [re] 应用 [match_eps_refl]，接着对结果解构并生成
    分类，其中你可以假设 [re] 匹配或不匹配空字符串。

    提示：如果你定义的 [regex_match] 对字符 [x] 和正则表达式 [re] 使用了 [derive]，
    那么可对 [x] 和 [re] 应用 [derive_corr]，以此证明 [x :: s =~ re] 当给定
    [s =~ derive x re] 时，反之亦然。 *)


Lemma match_eps_iff : forall re: reg_exp ascii, 
  [] =~ re <-> match_eps re = true.
Proof.
  intros re. apply reflect_iff.
  apply match_eps_refl.
Qed.



Theorem regex_refl : matches_regex regex_match.
Proof.
  unfold matches_regex. intros s.
  induction s as [| h t IHs].
  - intros re. apply iff_reflect. split.
    + intros H. simpl. apply match_eps_iff. apply H.
    + intros H. simpl in H. apply match_eps_iff. apply H.
  - intros re. apply iff_reflect. 
    remember (IHs (derive h re)) as IHs'.
    clear HeqIHs'. apply reflect_iff in IHs'. split.
    + intros H. apply derive_corr in H. simpl. 
      apply IHs'. apply H.
    + intros H. apply derive_corr. simpl in H. apply IHs'.
      apply H.
Qed.    