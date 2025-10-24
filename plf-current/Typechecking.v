(** * Typechecking: A Typechecker for STLC *)

(** The [has_type] relation of the STLC defines what it means for a
    term to belong to a type (in some context).  But it doesn't, by
    itself, give us an algorithm for _checking_ whether or not a term
    is well typed.

    Fortunately, the rules defining [has_type] are _syntax directed_
    -- that is, for every syntactic form of the language, there is
    just one rule that can be used to give a type to terms of that
    form.  This makes it straightforward to translate the typing rules
    into clauses of a typechecking _function_ that takes a term and a
    context and either returns the term's type or else signals that
    the term is not typable.  *)

(** This short chapter constructs such a function and proves it
    correct. *)

Set Warnings "-notation-overridden,-parsing".
From Coq Require Import Bool.Bool.
From PLF Require Import Maps.
From PLF Require Import Smallstep.
From PLF Require Import Stlc.
From PLF Require MoreStlc.

Module STLCTypes.
Export STLC.

(* ################################################################# *)
(** * Comparing Types *)

(** First, we need a function to compare two types for equality... *)

Fixpoint eqb_ty (T1 T2:ty) : bool :=
  match T1,T2 with
  | Bool, Bool =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | _,_ =>
      false
  end.

(** ... and we need to establish the usual two-way connection between
    the boolean result returned by [eqb_ty] and the logical
    proposition that its inputs are equal. *)

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1. induction T1; simpl.
    reflexivity.
    rewrite IHT1_1. rewrite IHT1_2. reflexivity.  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof with auto.
  intros T1. induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq.
  - (* T1=Bool *)
    reflexivity.
  - (* T1=Arrow T1_1 T1_2 *)
    rewrite andb_true_iff in H0. inversion H0 as [Hbeq1 Hbeq2].
    apply IHT1_1 in Hbeq1. apply IHT1_2 in Hbeq2. subst...  Qed.
End STLCTypes.

(* ################################################################# *)
(** * The Typechecker *)

(** The typechecker works by walking over the structure of the given
    term, returning either [Some T] or [None].  Each time we make a
    recursive call to find out the types of the subterms, we need to
    pattern-match on the results to make sure that they are not
    [None].  Also, in the [app] case, we use pattern matching to
    extract the left- and right-hand sides of the function's arrow
    type (and fail if the type of the function is not [Arrow T11 T12]
    for some [T11] and [T12]). *)

Module FirstTry.
Import STLCTypes.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      Gamma x
  | abs x T11 t12 =>
      match type_check (update Gamma x T11) t12 with
      | Some T12 => Some (Arrow T11 T12)
      | _ => None
      end
  | app t1 t2 =>
      match type_check Gamma t1, type_check Gamma t2 with
      | Some (Arrow T11 T12),Some T2 =>
          if eqb_ty T11 T2 then Some T12 else None
      | _,_ => None
      end
  | tru =>
      Some Bool
  | fls =>
      Some Bool
  | test guard t f =>
      match type_check Gamma guard with
      | Some Bool =>
          match type_check Gamma t, type_check Gamma f with
          | Some T1, Some T2 =>
              if eqb_ty T1 T2 then Some T1 else None
          | _,_ => None
          end
      | _ => None
      end
  end.

End FirstTry.

(* ################################################################# *)
(** * Digression: Improving the Notation *)

(** Before we consider the properties of this algorithm, let's write
    it out again in a cleaner way, using "monadic" notations in the
    style of Haskell to streamline the plumbing of options.  First, we
    define a notation for composing two potentially failing (i.e.,
    option-returning) computations: *)

Notation " x <- e1 ;; e2" := (match e1 with
                              | Some x => e2
                              | None => None
                              end)
         (right associativity, at level 60).

(** Second, we define [return] and [fail] as synonyms for [Some] and
    [None]: *)

Notation " 'return' e "
  := (Some e) (at level 60).
         
Notation " 'fail' "
  := None.

Module STLCChecker.
Import STLCTypes.

(** Now we can write the same type-checking function in a more
    imperative-looking style using these notations. *)

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | abs x T11 t12 =>
      T12 <- type_check (update Gamma x T11) t12 ;;
      return (Arrow T11 T12)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with 
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | tru =>
      return Bool
  | fls =>
      return Bool
  | test guard t1 t2 =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match Tguard with
      | Bool =>
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(* ################################################################# *)
(** * Properties *)

(** To verify that the typechecking algorithm is correct, we show that
    it is _sound_ and _complete_ for the original [has_type]
    relation -- that is, [type_check] and [has_type] define the same
    partial function. *)

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H. 
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    remember (type_check Gamma t1) as TO1.
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct T1 as [|T11 T12]; try solve_by_invert; 
    remember (type_check Gamma t2) as TO2;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T11 T2) eqn: Heqb.
    apply eqb_ty__eq in Heqb.
    inversion H0; subst...
    inversion H0.
  - (* abs *)
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as G'.
    remember (type_check G' t0) as TO2.
    destruct TO2; try solve_by_invert.
    inversion H0; subst...
  - (* tru *) eauto.
  - (* fls *) eauto.
  - (* test *)
    remember (type_check Gamma t1) as TOc.
    remember (type_check Gamma t2) as TO1.
    remember (type_check Gamma t3) as TO2.
    destruct TOc as [Tc|]; try solve_by_invert.
    destruct Tc; try solve_by_invert;
    destruct TO1 as [T1|]; try solve_by_invert;
    destruct TO2 as [T2|]; try solve_by_invert.
    destruct (eqb_ty T1 T2) eqn:Heqb;
    try solve_by_invert.
    apply eqb_ty__eq in Heqb.
    inversion H0. subst. subst...
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof with auto.
  intros Gamma t T Hty.
  induction Hty; simpl.
  - (* T_Var *) destruct (Gamma x0) eqn:H0; assumption.
  - (* T_Abs *) rewrite IHHty...
  - (* T_App *)
    rewrite IHHty1. rewrite IHHty2.
    rewrite (eqb_ty_refl T11)...
  - (* T_True *) eauto.
  - (* T_False *) eauto.
  - (* T_If *) rewrite IHHty1. rewrite IHHty2.
    rewrite IHHty3. rewrite (eqb_ty_refl T)...
Qed.

End STLCChecker.

(* ################################################################# *)
(** * Exercises *)

(** **** 练习：5 星, standard (typechecker_extensions) 

    In this exercise we'll extend the typechecker to deal with the
    extended features discussed in chapter [MoreStlc].  Your job
    is to fill in the omitted cases in the following. *)

Module TypecheckerExtensions.
(* 请勿修改下面这一行： *)
Definition manual_grade_for_type_checking_sound : option (nat*string) := None.
(* 请勿修改下面这一行： *)
Definition manual_grade_for_type_checking_complete : option (nat*string) := None.
Import MoreStlc.
Import STLCExtended.

Fixpoint eqb_ty (T1 T2 : ty) : bool :=
  match T1,T2 with
  | Nat, Nat =>
      true
  | Unit, Unit =>
      true
  | Arrow T11 T12, Arrow T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Prod T11 T12, Prod T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | Sum T11 T12, Sum T21 T22 =>
      andb (eqb_ty T11 T21) (eqb_ty T12 T22)
  | List T11, List T21 =>
      eqb_ty T11 T21
  | _,_ =>
      false
  end.

Lemma eqb_ty_refl : forall T1,
  eqb_ty T1 T1 = true.
Proof.
  intros T1.
  induction T1; simpl;
    try reflexivity;
    try (rewrite IHT1_1; rewrite IHT1_2; reflexivity);
    try (rewrite IHT1; reflexivity).  Qed.

Lemma eqb_ty__eq : forall T1 T2,
  eqb_ty T1 T2 = true -> T1 = T2.
Proof.
  intros T1.
  induction T1; intros T2 Hbeq; destruct T2; inversion Hbeq;
    try reflexivity;
    try (rewrite andb_true_iff in H0; inversion H0 as [Hbeq1 Hbeq2];
         apply IHT1_1 in Hbeq1; apply IHT1_2 in Hbeq2; subst; auto);
    try (apply IHT1 in Hbeq; subst; auto).
 Qed.

Fixpoint type_check (Gamma : context) (t : tm) : option ty :=
  match t with
  | var x =>
      match Gamma x with
      | Some T => return T
      | None   => fail
      end
  | abs x1 T1 t2 =>
      T2 <- type_check (update Gamma x1 T1) t2 ;;
      return (Arrow T1 T2)
  | app t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1 with 
      | Arrow T11 T12 =>
          if eqb_ty T11 T2 then return T12 else fail
      | _ => fail
      end
  | const _ =>
      return Nat
  | scc t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | prd t1 =>
      T1 <- type_check Gamma t1 ;;
      match T1 with 
      | Nat => return Nat
      | _ => fail
      end
  | mlt t1 t2 =>
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      match T1, T2 with
      | Nat, Nat => return Nat
      | _,_        => fail
      end
  | test0 guard t f =>
      Tguard <- type_check Gamma guard ;;
      T1 <- type_check Gamma t ;;
      T2 <- type_check Gamma f ;;
      match Tguard with
      | Nat => if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end

  (* Complete the following cases. *)
  
  (* sums *)
  | tinl T2 t1 => 
      match (type_check Gamma t1) with
      | Some (T1) => return Sum T1 T2
      | None => fail
      end
  | tinr T1 t2 =>
      match (type_check Gamma t2) with
      | Some (T2) => return Sum T1 T2
      | None => fail
      end 
  | tcase t0 x1 t1 x2 t2 =>
      T0 <- type_check Gamma t0 ;;
      match T0 with
      | Sum T1 T2 => 
          Tx1 <- type_check (update Gamma x1 T1) t1 ;;
          Tx2 <- type_check (update Gamma x2 T2) t2 ;;
          if eqb_ty Tx1 Tx2 then return Tx1 else fail
      | _ => fail
      end
  (* lists (the [tlcase] is given for free) *)
  | tnil T => return List T
  | tcons t1 t2 => 
      match type_check Gamma t1, type_check Gamma t2 with
      | Some T1, Some (List T2) =>
          if eqb_ty T1 T2 then return List T1 else fail
      | _, _ => fail
      end
  | tlcase t0 t1 x21 x22 t2 =>
      match type_check Gamma t0 with
      | Some (List T) =>
          match type_check Gamma t1,
                type_check (update (update Gamma x22 (List T)) x21 T) t2 with
          | Some T1', Some T2' =>
              if eqb_ty T1' T2' then Some T1' else None
          | _,_ => None
          end
      | _ => None
      end
  (* unit *)
  | unit => return Unit
  (* pairs *)
  | pair t1 t2 => 
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check Gamma t2 ;;
      return Prod T1 T2
  | fst t =>
      match type_check Gamma t with
      | Some (Prod T1 T2) => return T1
      | _ => fail
      end
  | snd t =>
      match type_check Gamma t with
      | Some (Prod T1 T2) => return T2
      | _ => fail
      end
  (* let *)
  | tlet x t1 t2 => 
      T1 <- type_check Gamma t1 ;;
      T2 <- type_check (update Gamma x T1) t2 ;;
      return T2  
  (* fix *)
  | tfix t =>
      match (type_check Gamma t) with 
      | Some (Arrow T1 T2) => 
          if eqb_ty T1 T2 then return T1 else fail
      | _ => fail
      end
  end.

(** Just for fun, we'll do the soundness proof with just a bit more
    automation than above, using these "mega-tactics": *)

Ltac invert_typecheck Gamma t T :=
  remember (type_check Gamma t) as TO;
  destruct TO as [T|]; 
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac analyze T T1 T2 :=
  destruct T as [T1 T2| |T1 T2|T1| |T1 T2]; try solve_by_invert.

Ltac fully_invert_typecheck Gamma t T T1 T2 :=
  let TX := fresh T in
  remember (type_check Gamma t) as TO;
  destruct TO as [TX|]; try solve_by_invert;
  destruct TX as [T1 T2| |T1 T2|T1| |T1 T2];
  try solve_by_invert; try (inversion H0; eauto); try (subst; eauto).

Ltac case_equality S T :=
  destruct (eqb_ty S T) eqn: Heqb;
  inversion H0; apply eqb_ty__eq in Heqb; subst; subst; eauto.

Theorem type_checking_sound : forall Gamma t T,
  type_check Gamma t = Some T -> has_type Gamma t T.
Proof with eauto.
  intros Gamma t. generalize dependent Gamma.
  induction t; intros Gamma T Htc; inversion Htc.
  - (* var *) rename s into x. destruct (Gamma x) eqn:H. 
    rename t into T'. inversion H0. subst. eauto. solve_by_invert.
  - (* app *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12.
    case_equality T11 T2.
  - (* abs *)
    rename s into x. rename t into T1.
    remember (update Gamma x T1) as Gamma'.
    invert_typecheck Gamma' t0 T0.
  - (* const *) eauto.
  - (* scc *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* prd *)
    rename t into t1.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
  - (* mlt *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T1 T11 T12; analyze T2 T21 T22.
    inversion H0. subst. eauto.
  - (* test0 *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    invert_typecheck Gamma t3 T3.
    destruct T1; try solve_by_invert.
    case_equality T2 T3.
  - (* tinl *) 
    invert_typecheck Gamma t0 T0.
  - (* tinr *)
    invert_typecheck Gamma t0 T0.
  - (* tcase *)
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck (update Gamma s T11) t2 T2.
    invert_typecheck (update Gamma s0 T12) t3 T3.
    case_equality T2 T3.
  - (* tnil *)
    constructor.
  - (* tcons *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
    analyze T2 T21 T22.
    case_equality T1 T21.
  - (* tlcase *)
    rename s into x31. rename s0 into x32.
    fully_invert_typecheck Gamma t1 T1 T11 T12.
    invert_typecheck Gamma t2 T2.
    remember (update (update Gamma x32 (List T11)) x31 T11) as Gamma'2.
    invert_typecheck Gamma'2 t3 T3.
    case_equality T2 T3.
  - (* unit *)
    constructor.
  - (* pair *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck Gamma t2 T2.
  - (* fst *)
    fully_invert_typecheck Gamma t T1 T11 T12.
  - (* snd *)
    fully_invert_typecheck Gamma t T1 T11 T12.
  - (* tlet *)
    invert_typecheck Gamma t1 T1.
    invert_typecheck (update Gamma s T1) t2 T2.
  - (* tfix *)
    fully_invert_typecheck Gamma t T1 T11 T12.
    case_equality T11 T12.
Qed.

Theorem type_checking_complete : forall Gamma t T,
  has_type Gamma t T -> type_check Gamma t = Some T.
Proof.
  intros Gamma t T Hty.
  induction Hty; simpl;
    try (rewrite IHHty);
    try (rewrite IHHty1);
    try (rewrite IHHty2);
    try (rewrite IHHty3);
    try (rewrite (eqb_ty_refl T)); 
    try (rewrite (eqb_ty_refl T1)); 
    try (rewrite (eqb_ty_refl T2)); 
    eauto.
  - destruct (Gamma x); try solve_by_invert. eauto.
Qed.

End TypecheckerExtensions.
(** [] *)

(** **** 练习：5 星, standard, optional (stlc_step_function) 

    Above, we showed how to write a typechecking function and prove it
    sound and complete for the typing relation.  Do the same for the
    operational semantics -- i.e., write a function [stepf] of type
    [tm -> option tm] and prove that it is sound and complete with
    respect to [step] from chapter [MoreStlc]. *)

Module StepFunction.
Import MoreStlc.
Import STLCExtended.

Fixpoint bvalue (t : tm) : bool :=
  match t with
  | abs _ _ _ => true
  | const _ => true
  | tinl _ v => bvalue v
  | tinr _ v => bvalue v 
  | tnil _ => true
  | tcons v1 vl => bvalue v1 && bvalue vl
  | unit => true
  | pair v1 v2 => bvalue v1 && bvalue v2
  | _ => false
  end.

Lemma bvalue_is_value : forall t,
    bvalue t = true <-> value t.
Proof with eauto.
  intros. split.
  - induction t; simpl; intros; try discriminate...
    + rewrite andb_true_iff in H. destruct H...
    + rewrite andb_true_iff in H. destruct H...
  - induction t; intros; try solve_by_invert...
    + inversion H...
    + inversion H...
    + simpl; rewrite andb_true_iff. inversion H...
    + simpl; rewrite andb_true_iff. inversion H...
Qed.

Hint Rewrite bvalue_is_value.

(* Operational semantics as a Coq function. *)
Fixpoint stepf (t : tm) : option tm :=
  match t with
  | var x => fail
  | abs x1 T1 t2 => fail
  | app t1 t2 =>
      match (stepf t1) with
      | Some t1' => return app t1' t2
      | _ => match (stepf t2) with
             | Some t2' => if bvalue t1 then return app t1 t2' else fail
             | _ => match t1 with 
                    | abs x T t => if bvalue t2 then return [x:=t2] t else fail 
                    | _ => fail
                    end
             end
      end
  | const _ => fail
  | scc t1 =>
      match (stepf t1) with
      | Some t1' => return scc t1'
      | _ => match t1 with
             | const n => return const (S n)
             | _ => fail
             end
      end
  | prd t1 =>
      match (stepf t1) with
      | Some t1' => return prd t1'
      | _ => match t1 with
             | const n => return const (pred n)
             | _ => fail
             end
      end
  | mlt t1 t2 => 
      match (stepf t1) with
      | Some t1' => return mlt t1' t2
      | _ => match (stepf t2) with
             | Some t2' => if bvalue t1 then return mlt t1 t2' else fail
             | _ => match t1, t2 with
                    | const n1, const n2 => return const (n1 * n2)
                    | _, _ => fail
                    end
             end
      end
  | test0 guard t f =>
      match (stepf guard) with
      | Some guard' => return test0 guard' t f
      | _ => match guard with
             | const O => return t
             | const (S n) => return f
             | _ => fail
             end
      end
  (* Complete the following cases. *)
  
  (* sums *)
  | tinl T2 t1 => 
      match (stepf t1) with
      | Some t1' => return tinl T2 t1'
      | _ => fail
      end
  | tinr T1 t2 =>
      match (stepf t2) with
      | Some t2' => return tinr T1 t2'
      | _ => fail
      end
  | tcase t0 x1 t1 x2 t2 =>
      match (stepf t0) with
      | Some t0' => return tcase t0' x1 t1 x2 t2
      | _ => match t0 with
             | tinl _ t11 => if bvalue t0 then return [x1:=t11] t1 else fail
             | tinr _ t21 => if bvalue t0 then return [x2:=t21] t2 else fail
             | _ => fail
             end
      end 
  (* lists (the [tlcase] is given for free) *)
  | tnil T => fail
  | tcons t1 t2 => 
      match (stepf t1) with
      | Some t1' => return tcons t1' t2
      | _ => match (stepf t2) with
             | Some t2' => if bvalue t1 then return tcons t1 t2' else fail
             | _ => fail
             end
      end
  | tlcase t0 t1 x21 x22 t2 =>
      match (stepf t0) with
      | Some t0' => return tlcase t0' t1 x21 x22 t2
      | _ => match t0 with
             | tnil _ => return t1
             | tcons v1 vl => if bvalue v1 && bvalue vl then 
                                  return [x22:=vl] [x21:=v1] t2 
                                  else fail
             | _ => fail
             end
      end
  (* unit *)
  | unit => fail
  (* pairs *)
  | pair t1 t2 =>
      match (stepf t1) with
      | Some t1' => return pair t1' t2
      | _ => match (stepf t2) with
             | Some t2' => if bvalue t1 then return pair t1 t2' else fail
             | _ => fail
             end
      end
  | fst t =>
      match (stepf t) with
      | Some t' => return fst t'
      | _ => match t with
             | pair t1 t2 => if bvalue t1 && bvalue t2 then return t1 else fail
             | _ => fail
             end
      end
  | snd t =>
      match (stepf t) with
      | Some t' => return snd t'
      | _ => match t with
             | pair t1 t2 => if bvalue t1 && bvalue t2 then return t2 else fail
             | _ => fail
             end
      end
  (* let *)
  | tlet x t1 t2 => 
      match (stepf t1) with
      | Some t1' => return tlet x t1' t2
      | _ => if bvalue t1 then return [x:=t1] t2 else fail
      end
  (* fix *)
  | tfix t =>
      match (stepf t) with
      | Some t' => return tfix t'
      | _ => match t with
             | abs f T t1 => return [f:=(tfix t)] t1
             | _ => fail
             end
      end
  end.

(* Soundness of [stepf]. *) 
Theorem sound_stepf : forall t t',
    stepf t = Some t'  ->  t --> t'.
Proof with eauto.
  intros t. induction t; intros; try solve_by_invert.
  - inversion H. destruct (stepf t1) eqn:Eq.
    + inversion H1...
    + destruct (stepf t2). destruct (bvalue t1) eqn:Eb; try discriminate.
      * inversion H1; subst. apply ST_App2... apply bvalue_is_value in Eb... 
      * destruct t1; try discriminate. destruct (bvalue t2) eqn:Eb; try discriminate. 
        inversion H1; subst. apply bvalue_is_value in Eb...
  - inversion H. destruct (stepf t) eqn:Eq.
    + inversion H1...
    + destruct t; try discriminate. inversion H1...
  - inversion H. destruct (stepf t) eqn:Eq.
    + inversion H1...
    + destruct t; try discriminate. inversion H1...
  - inversion H. destruct (stepf t1).
    + inversion H1...
    + destruct (stepf t2).
      * destruct (bvalue t1) eqn:Eb; try discriminate. apply bvalue_is_value in Eb.
        inversion H1...
      * destruct t1; try discriminate. destruct t2; try discriminate.
        inversion H1...
  - inversion H. destruct (stepf t1). 
    + inversion H1...
    + destruct t1; try discriminate. destruct n; inversion H1...
  - inversion H. destruct (stepf t0); try discriminate. inversion H1...
  - inversion H. destruct (stepf t0); try discriminate. inversion H1...
  - inversion H. destruct (stepf t1); try discriminate. inversion H1...
    destruct t1; try discriminate. inversion H1; subst.
    destruct (bvalue t1) eqn:Et; try discriminate. apply bvalue_is_value in Et. 
    inversion H2... destruct (bvalue (tinr t t1)) eqn:Er; try discriminate.
    apply bvalue_is_value in Er. inversion Er; subst. inversion H1... 
  - inversion H. destruct (stepf t1); try discriminate.
    + inversion H1...
    + destruct (stepf t2); try discriminate. destruct (bvalue t1) eqn:Eb; try discriminate.
      apply bvalue_is_value in Eb. inversion H1...
  - inversion H. destruct (stepf t1); try discriminate.
    + inversion H1...
    + destruct t1; try discriminate.
      * inversion H1...
      * destruct (bvalue t1_1) eqn:Et1; try discriminate.
        destruct (bvalue t1_2) eqn:Et2; try discriminate.
        apply bvalue_is_value in Et1. apply bvalue_is_value in Et2.
        inversion H1...
  - inversion H. destruct (stepf t1); try discriminate. 
    + inversion H1...
    + destruct (stepf t2); try discriminate.
      destruct (bvalue t1) eqn:Et; try discriminate.
      apply bvalue_is_value in Et. inversion H1...
  - inversion H. destruct (stepf t); try discriminate.
    + inversion H1...
    + destruct t; try discriminate.
      destruct (bvalue t1) eqn:Et1; try discriminate.
      destruct (bvalue t2) eqn:Et2; try discriminate.
      apply bvalue_is_value in Et1. apply bvalue_is_value in Et2.
      inversion H1; subst... 
  - inversion H. destruct (stepf t); try discriminate.
    + inversion H1...
    + destruct t; try discriminate.
      destruct (bvalue t1) eqn:Et1; try discriminate.
      destruct (bvalue t2) eqn:Et2; try discriminate.
      apply bvalue_is_value in Et1. apply bvalue_is_value in Et2.
      inversion H1; subst...
  - inversion H. destruct (stepf t1); try discriminate.
    + inversion H1... 
    + destruct (bvalue t1) eqn:Et; try discriminate.
      apply bvalue_is_value in Et. inversion H1...
  - inversion H. destruct (stepf t); try discriminate.
    + inversion H1...
    + destruct t; try discriminate.
      inversion H1...
Qed.

Lemma value_is_fail : forall t,
    value t -> stepf t = fail.
Proof with eauto.
  intros t. induction t; intros; try solve_by_invert; eauto.
  - inversion H; subst. simpl. rewrite IHt...
  - inversion H; subst. simpl; rewrite IHt...
  - inversion H; subst. simpl; rewrite IHt1... rewrite IHt2...
  - inversion H; subst. simpl; rewrite IHt1... rewrite IHt2...
Qed.

(* Completeness of [stepf]. *)
Theorem complete_stepf : forall t t',
    t --> t'  ->  stepf t = Some t'.
Proof with eauto.
  intros t. induction t; intros t' H; try solve_by_invert.
  - inversion H.
    + simpl. remember H3; clear Heqv. apply value_is_fail in H3. rewrite H3.
      apply bvalue_is_value in v. rewrite v...
    + simpl. rewrite (IHt1 t1')...
    + simpl. remember H2; clear Heqv.
      apply value_is_fail in H2. rewrite H2. rewrite (IHt2 t2')...
      apply bvalue_is_value in v. rewrite v...
  - inversion H...
    simpl. rewrite (IHt t1')...
  - inversion H... simpl; rewrite (IHt t1')...
  - inversion H...
    + simpl. rewrite (IHt1 t1')...
    + simpl. remember H2; clear Heqv.
      apply value_is_fail in H2. rewrite H2. rewrite (IHt2 t2')...
      apply bvalue_is_value in v. rewrite v...
  - inversion H... simpl. rewrite (IHt1 t1')...
  - inversion H... simpl. rewrite (IHt t1')...
  - inversion H... simpl. rewrite (IHt t1')...
  - inversion H; subst...
    + simpl. rewrite (IHt1 t0')...
    + simpl. remember H6; clear Heqv.
      apply value_is_fail in H6. rewrite H6. 
      apply bvalue_is_value in v. rewrite v...
    + simpl. remember H6; clear Heqv.
      apply value_is_fail in H6. rewrite H6. 
      apply bvalue_is_value in v. rewrite v...
  - inversion H; subst... 
    + simpl. rewrite (IHt1 t1')...
    + simpl. remember H2; clear Heqv.
      apply value_is_fail in H2. rewrite H2. rewrite (IHt2 t2')...
      apply bvalue_is_value in v. rewrite v...
  - inversion H; subst...
    + simpl. rewrite (IHt1 t1')...
    + simpl. remember H6; clear Heqv.
      apply value_is_fail in H6. rewrite H6. 
      apply bvalue_is_value in v. rewrite v...
      remember H7; clear Heqv0.
      apply value_is_fail in H7. rewrite H7. 
      apply bvalue_is_value in v0. rewrite v0...
  - inversion H; subst.
    + simpl. rewrite (IHt1 t1')...
    + simpl. remember H2; clear Heqv.
      apply value_is_fail in H2. rewrite H2. 
      apply bvalue_is_value in v. rewrite v...
      rewrite (IHt2 t2')...
  - inversion H; subst.
    + simpl. rewrite (IHt t1')...
    + simpl. remember H1; clear Heqv.
      apply value_is_fail in H1. rewrite H1. 
      apply bvalue_is_value in v. rewrite v...
      remember H2; clear Heqv0.
      apply value_is_fail in H2. rewrite H2. 
      apply bvalue_is_value in v0. rewrite v0...
  - inversion H; subst.
    + simpl. rewrite (IHt t1')...
    + simpl. remember H1; clear Heqv.
      apply value_is_fail in H1. rewrite H1. 
      apply bvalue_is_value in v. rewrite v...
      remember H2; clear Heqv0.
      apply value_is_fail in H2. rewrite H2. 
      apply bvalue_is_value in v0. rewrite v0...
  - inversion H; subst.
    + simpl. rewrite (IHt1 t1')...
    + simpl. remember H4; clear Heqv.
      apply value_is_fail in H4. rewrite H4. 
      apply bvalue_is_value in v. rewrite v...
  - inversion H; subst...
    simpl. rewrite (IHt t1')...
Qed.
     

End StepFunction.
(** [] *)

(** **** 练习：5 星, standard, optional (stlc_impl) 

    Using the Imp parser described in the [ImpParser] chapter
    of _Logical Foundations_ as a guide, build a parser for extended
    STLC programs.  Combine it with the typechecking and stepping
    functions from the above exercises to yield a complete typechecker
    and interpreter for this language. *)

Module StlcImpl.
Import StepFunction.

(* 请在此处解答 *)
End StlcImpl.
(** [] *)

(* 2022-03-14 05:28:23 (UTC+00) *)
