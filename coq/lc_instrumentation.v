From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Decidable.
Import ListNotations.


(* based on STLCRef chapter of Software Foundations *)

(* terms *)
Inductive tm  : Type :=
  | var    : string -> tm
  | app    : tm -> tm -> tm
  | abs    : string -> tm -> tm
  | const  : nat -> tm
  | scc    : tm -> tm
  | prd    : tm -> tm
  | test0  : tm -> tm -> tm -> tm
  | unit   : tm
  | ref    : tm -> tm
  | deref  : tm -> tm
  | assign : tm -> tm -> tm
  | loc    : nat -> tm
  | error  : string -> tm.


(* values *)
Inductive value : tm -> Prop :=
  | v_abs  : forall x t,
      value (abs x t)
  | v_nat : forall n,
      value (const n)
  | v_unit :
      value unit
  | v_loc : forall l,
      value (loc l).
Hint Constructors value.

Fixpoint valueb (t : tm) : bool :=
  match t with
  | abs _ _ | const _ | unit | loc _ => true
  | _ => false
  end.

Theorem valueb_sound : forall t, value t -> (valueb t = true).
Proof.
  intros.
  inversion H; simpl; reflexivity.
Qed.

Theorem valueb_complete : forall t, (valueb t = true) -> value t.
Proof.
  intros.
  destruct t; simpl; try discriminate; auto.
Qed.

(* substitution. NB ignores free-variable issues. *)
Fixpoint subst (x:string) (s:tm) (t:tm) : tm :=
  match t with
  | var x'       =>
      if String.eqb x x' then s else t
  | app t1 t2    =>
      app (subst x s t1) (subst x s t2)
  | abs x' t1  =>
      if String.eqb x x' then t else abs x' (subst x s t1)
  | const n        =>
      t
  | scc t1      =>
      scc (subst x s t1)
  | prd t1      =>
      prd (subst x s t1)
  | test0 t1 t2 t3 =>
      test0 (subst x s t1) (subst x s t2) (subst x s t3)
  | unit         =>
      t
  | ref t1       =>
      ref (subst x s t1)
  | deref t1     =>
      deref (subst x s t1)
  | assign t1 t2 =>
      assign (subst x s t1) (subst x s t2)
  | loc _        =>
      t
  | error _      => t 
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(* equivalent to `t1; t2` *)
Definition tseq t1 t2 :=
  app (abs "x" t2) t1.


(* store-based substitution semantics *)

(* stores *)
Definition store := list tm.

Definition store_lookup (n:nat) (st:store) :=
  nth n st unit.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.


Reserved Notation "t1 '/' st1 '-->' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Import ListNotations.

Inductive step : tm * store -> tm * store -> Prop :=
  | ST_AppAbs : forall x t12 v2 st,
         value v2 ->
         app (abs x t12) v2 / st --> [x:=v2]t12 / st
  | ST_App1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         app t1 t2 / st --> app t1' t2 / st'
  | ST_App2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         app v1 t2 / st --> app v1 t2'/ st'
  | ST_SuccNat : forall n st,
         scc (const n) / st --> const (S n) / st
  | ST_Succ : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         scc t1 / st --> scc t1' / st'
  | ST_PredNat : forall n st,
         prd (const n) / st --> const (pred n) / st
  | ST_Pred : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         prd t1 / st --> prd t1' / st'
  | ST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         test0 t1 t2 t3 / st --> test0 t1' t2 t3 / st'
  | ST_If0_Zero : forall t2 t3 st,
         test0 (const 0) t2 t3 / st --> t2 / st
  | ST_If0_Nonzero : forall n t2 t3 st,
         test0 (const (S n)) t2 t3 / st --> t3 / st
  | ST_RefValue : forall v1 st,
         value v1 ->
         ref v1 / st --> loc (length st) / (st ++ v1::nil)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         ref t1 /  st --> ref t1' /  st'
  | ST_DerefLoc : forall st l,
         l < length st ->
         deref (loc l) / st --> store_lookup l st / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         deref t1 / st --> deref t1' / st'
  | ST_Assign : forall v2 l st,
         value v2 ->
         l < length st ->
         assign (loc l) v2 / st --> unit / replace l v2 st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         assign t1 t2 / st --> assign t1' t2 / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         assign v1 t2 / st --> assign v1 t2' / st'

where "t1 '/' st1 '-->' t2 '/' st2" := (step (t1,st1) (t2,st2)).
Hint Constructors step.

Definition relation (X : Type) := X -> X -> Prop.
Inductive multi {X : Type} (R : relation X) : relation X :=
  | multi_refl : forall (x : X), multi R x x
  | multi_step : forall (x y z : X),
                    R x y ->
                    multi R y z ->
                    multi R x z.

Hint Constructors step.
Definition multistep := (multi step).
Notation "t1 '/' st '-->*' t2 '/' st'" :=
               (multistep (t1,st) (t2,st'))
               (at level 40, st at level 39, t2 at level 39).


Fixpoint stepfn (t : tm) (s : store) : tm * store :=
  match t with
  | var _ | unit | const _ | abs _ _ | loc _ | error _ => (t,s)
  | app fn arg =>
    if (valueb fn) then
      if (valueb arg) then
        match fn with
        | abs x body => (subst x arg body, s)
        | _ => (error "attempt to apply non-fn", s)
        end
      else
        let (arg',s') := stepfn arg s in
        (app fn arg', s')
    else
      let (fn',s') := stepfn fn s in
      (app fn' arg, s')
  | scc t1 =>
    if (valueb t1) then
      match t1 with
      | const n => (const (S n), s)
      | _ => (error "scc of non nat", s)
      end
    else
      let (t1', s') := stepfn t1 s in
      (scc t1', s')
  | prd t1 =>
    if (valueb t1) then
      match t1 with
      | const n => (const (pred n), s)
      | _ => (error "prd of non nat", s)
      end
    else
      let (t1', s') := stepfn t1 s in
      (prd t1', s')
  | test0 cond yes no =>
    if (valueb cond) then
      match cond with
      | const 0 => (yes, s)
      | const (S n) => (no, s)
      | _ => (error "test0 of non nat", s)
      end
    else
      let (cond', s') := stepfn cond s in
      (test0 cond' yes no, s')
  | ref t1 =>
    if (valueb t1) then
      (loc (length s), (s ++ t1::nil))
    else
      let (t1', s') := stepfn t1 s in
      (ref t1', s')
  | deref t1 =>
    if (valueb t1) then
      match t1 with
      | loc l =>
        if Nat.ltb l (length s) then
          (store_lookup l s, s)
        else (error "attempt to deref invalid loc", s)
      | _ => (error "attempt to deref non-loc", s)
      end
    else
      let (t1', s') := stepfn t1 s in
      (deref t1', s')
  | assign t1 t2 =>
    if (valueb t1) then
      if (valueb t2) then
        match t1 with
        | loc l =>
          if  Nat.ltb l (length s) then
            (unit, replace l t2 s)
          else (error "attempt to assign invalid loc", s)
        | _ => (error "attempt to assign non-loc", s)
        end
      else
        let (t2', s') := stepfn t2 s in
        (assign t1 t2', s')
    else
      let (t1', s') := stepfn t1 s in
      (assign t1' t2, s')   
  end.


Lemma step_not_value : forall t s t' s',
    t / s --> t' / s' -> ~(value t).
Proof.
  intros; inversion H; subst; intuition; inversion H0.
Qed.
 
Lemma not_valueb_sound : forall t, ~(value t) -> valueb t = false.
Proof.
  intros.
  destruct t; simpl; try reflexivity; try contradict H; constructor.
Qed.


Ltac stepfn_sound_tac1 :=
  match goal with
  | [ H : ?t / ?s --> ?t' / ?s' |- _ ] =>
    specialize (not_valueb_sound t) as NV;
    specialize (step_not_value t s t' s' H) as VBS;
    intros
  | _ => idtac
  end.
      
Ltac stepfn_sound_tac2 :=
  match goal with
  | [ H1 : ~ value ?t -> valueb ?t = false,
      H2 : ~ value ?t |- _ ] =>
    specialize (H1 H2); rewrite H1
  | _ => idtac
  end.

Ltac stepfn_sound_tac3 :=
  match goal with
  | [ H : value ?t |- _ ] =>
    apply valueb_sound in H; rewrite H
  end.

Ltac stepfn_sound_tac4 :=
  match goal with
  | [ H : (forall _ _ _, (?t / _ --> _ / _) -> _),
      H1 : ?t / ?s --> ?t' / ?s' |- _] =>
    specialize (H s t' s' H1); now rewrite H
  | [ H : (forall _ _ _, (?t / _ --> _ / _) -> _) |- _ ] => auto
  end.
                                     
Ltac stepfn_sound_tac :=
  stepfn_sound_tac1; stepfn_sound_tac2;
  try stepfn_sound_tac3; try stepfn_sound_tac4.

Theorem stepfn_sound : forall t1 s1 t2 s2,
    t1 / s1 --> t2 / s2 -> stepfn t1 s1 = (t2, s2).
Proof.
  intros t1.
  induction t1; intros; inversion H; subst; simpl; stepfn_sound_tac.
  - apply Nat.ltb_lt in H1. now rewrite H1.
  - apply Nat.ltb_lt in H6. now rewrite H6.
Qed.



(* --------------------------------------------------- *)
(* META LANGUAGE - add counters to stores, incremented each time
   the loc is refed, derefed, or assigned *)


Inductive mtm : Type :=
  | mvar    : string -> mtm
  | mapp    : mtm -> mtm -> mtm
  | mabs    : string -> mtm -> mtm
  | mconst  : nat -> mtm
  | mscc    : mtm -> mtm
  | mprd    : mtm -> mtm
  | mtest0  : mtm -> mtm -> mtm -> mtm
  | munit   : mtm
  | mref    : mtm -> mtm
  | mderef  : mtm -> mtm
  | massign : mtm -> mtm -> mtm
  | mloc    : nat -> mtm
  | merror  : string -> mtm.

(* values *)
Inductive mvalue : mtm -> Prop :=
  | mv_abs  : forall x t,
      mvalue (mabs x t)
  | mv_nat : forall n,
      mvalue (mconst n)
  | mv_unit :
      mvalue munit
  | mv_loc : forall l,
      mvalue (mloc l).
Hint Constructors mvalue.

Fixpoint mvalueb (mt : mtm) : bool :=
  match mt with
  | mabs _ _ | mconst _ | munit | mloc _ => true
  | _ => false
  end.

Theorem mvalueb_sound : forall mt, mvalue mt -> (mvalueb mt = true).
Proof.
  intros.
  inversion H; simpl; reflexivity.
Qed.

Theorem mvalueb_complete : forall mt, (mvalueb mt = true) -> mvalue mt.
Proof.
  intros.
  destruct mt; simpl; try discriminate; auto.
Qed.

(* substitution. NB ignores free-variable issues. *)
Fixpoint msubst (x:string) (s:mtm) (t:mtm) : mtm :=
  match t with
  | mvar x'       =>
      if String.eqb x x' then s else t
  | mapp t1 t2    =>
      mapp (msubst x s t1) (msubst x s t2)
  | mabs x' t1  =>
      if String.eqb x x' then t else mabs x' (msubst x s t1)
  | mconst n        =>
      t
  | mscc t1      =>
      mscc (msubst x s t1)
  | mprd t1      =>
      mprd (msubst x s t1)
  | mtest0 t1 t2 t3 =>
      mtest0 (msubst x s t1) (msubst x s t2) (msubst x s t3)
  | munit         =>
      t
  | mref t1       =>
      mref (msubst x s t1)
  | mderef t1     =>
      mderef (msubst x s t1)
  | massign t1 t2 =>
      massign (msubst x s t1) (msubst x s t2)
  | mloc _        =>
      t
  | merror _      => t 
  end.


Definition mstore := list (mtm * nat).

Definition mstore_lookup (n:nat) (mst:mstore) :=
  match nth n mst (munit, O) with
  | (mt, _) => mt
  end.

Definition mstore_incr_loc (n:nat) (mst:mstore) :=
  match nth n mst (munit, O) with
  | (mt, ct) => replace n (mt, S ct) mst
  end. 

Definition replace_incr_loc (n:nat) (t:mtm) (mst:mstore) :=
  match nth n mst (munit, O) with
  | (_, ct) => replace n (t, S ct) mst
  end. 

Reserved Notation "t1 '/' st1 '-m>' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive metastep : mtm * mstore -> mtm * mstore -> Prop :=
  | MST_AppAbs : forall x t12 v2 st,
         mvalue v2 ->
         mapp (mabs x t12) v2 / st -m> msubst x v2 t12 / st
  | MST_App1 : forall t1 t1' t2 st st',
         t1 / st -m> t1' / st' ->
         mapp t1 t2 / st -m> mapp t1' t2 / st'
  | MST_App2 : forall v1 t2 t2' st st',
         mvalue v1 ->
         t2 / st -m> t2' / st' ->
         mapp v1 t2 / st -m> mapp v1 t2'/ st'
  | MST_SuccNat : forall n st,
         mscc (mconst n) / st -m> mconst (S n) / st
  | MST_Succ : forall t1 t1' st st',
         t1 / st -m> t1' / st' ->
         mscc t1 / st -m> mscc t1' / st'
  | MST_PredNat : forall n st,
         mprd (mconst n) / st -m> mconst (pred n) / st
  | MST_Pred : forall t1 t1' st st',
         t1 / st -m> t1' / st' ->
         mprd t1 / st -m> mprd t1' / st'
  | MST_If0 : forall t1 t1' t2 t3 st st',
         t1 / st -m> t1' / st' ->
         mtest0 t1 t2 t3 / st -m> mtest0 t1' t2 t3 / st'
  | MST_If0_Zero : forall t2 t3 st,
         mtest0 (mconst 0) t2 t3 / st -m> t2 / st
  | MST_If0_Nonzero : forall n t2 t3 st,
         mtest0 (mconst (S n)) t2 t3 / st -m> t3 / st
  | MST_Refvalue : forall v1 st,
         mvalue v1 ->
         mref v1 / st -m> mloc (length st) / (st ++ (v1,0)::nil)
  | MST_Ref : forall t1 t1' st st',
         t1 / st -m> t1' / st' ->
         mref t1 /  st -m> mref t1' /  st'
  | MST_DerefLoc : forall st l,
         l < length st ->
         mderef (mloc l) / st -m> mstore_lookup l st / mstore_incr_loc l st
  | MST_Deref : forall t1 t1' st st',
         t1 / st -m> t1' / st' ->
         mderef t1 / st -m> mderef t1' / st'
  | MST_Assign : forall v2 l st,
         mvalue v2 ->
         l < length st ->
         massign (mloc l) v2 / st -m> munit / replace_incr_loc l v2 st
  | MST_Assign1 : forall t1 t1' t2 st st',
         t1 / st -m> t1' / st' ->
         massign t1 t2 / st -m> massign t1' t2 / st'
  | MST_Assign2 : forall v1 t2 t2' st st',
         mvalue v1 ->
         t2 / st -m> t2' / st' ->
         massign v1 t2 / st -m> massign v1 t2' / st'
where "t1 '/' st1 '-m>' t2 '/' st2" := (metastep (t1,st1) (t2,st2)).
Hint Constructors metastep.

Fixpoint mstepfn (t : mtm) (s : mstore) : mtm * mstore :=
  match t with
  | mvar _ | munit | mconst _ | mabs _ _ | mloc _ | merror _ => (t,s)
  | mapp fn arg =>
    if (mvalueb fn) then
      if (mvalueb arg) then
        match fn with
        | mabs x body => (msubst x arg body, s)
        | _ => (merror "attempt to apply non-fn", s)
        end
      else
        let (arg',s') := mstepfn arg s in
        (mapp fn arg', s')
    else
      let (fn',s') := mstepfn fn s in
      (mapp fn' arg, s')
  | mscc t1 =>
    if (mvalueb t1) then
      match t1 with
      | mconst n => (mconst (S n), s)
      | _ => (merror "scc of non nat", s)
      end
    else
      let (t1', s') := mstepfn t1 s in
      (mscc t1', s')
  | mprd t1 =>
    if (mvalueb t1) then
      match t1 with
      | mconst n => (mconst (pred n), s)
      | _ => (merror "prd of non nat", s)
      end
    else
      let (t1', s') := mstepfn t1 s in
      (mprd t1', s')
  | mtest0 cond yes no =>
    if (mvalueb cond) then
      match cond with
      | mconst 0 => (yes, s)
      | mconst (S n) => (no, s)
      | _ => (merror "test0 of non nat", s)
      end
    else
      let (cond', s') := mstepfn cond s in
      (mtest0 cond' yes no, s')
  (* Add instrumentation to the store *)
  | mref t1 =>
    if (mvalueb t1) then
      (mloc (length s), (s ++ (t1,0)::nil))
    else
      let (t1', s') := mstepfn t1 s in
      (mref t1', s')
  | mderef t1 =>
    if (mvalueb t1) then
      match t1 with
      | mloc l =>
        if Nat.ltb l (length s) then
          (mstore_lookup l s, mstore_incr_loc l s)
        else (merror "attempt to deref invalid loc", s)
      | _ => (merror "attempt to deref non-loc", s)
      end
    else
      let (t1', s') := mstepfn t1 s in
      (mderef t1', s')
  | massign t1 t2 =>
    if (mvalueb t1) then
      if (mvalueb t2) then
        match t1 with
        | mloc l =>
          if Nat.ltb l (length s) then
            (munit, replace_incr_loc l t2 s)
          else (merror "attempt to assign invalid loc", s)
        | _ => (merror "attempt to assign non-loc", s)
        end
      else
        let (t2', s') := mstepfn t2 s in
        (massign t1 t2', s')
    else
      let (t1', s') := mstepfn t1 s in
      (massign t1' t2, s')   
  end.

Theorem mstepfn_sound :
  forall mt ms mt' ms',
    mt / ms -m> mt' / ms' ->
    mstepfn mt ms = (mt', ms').
Proof.
  intros mt; induction mt; intros; subst; simpl; inversion H; admit.
  (* todo - same as stepfn_sound *)
Admitted.

Inductive reify_tm : tm -> mtm -> Prop :=
| Reify_Var :
    forall x, reify_tm (var x) (mvar x)
| Reify_App :
    forall t1 t2 mt1 mt2,
      reify_tm t1 mt1 -> reify_tm t2 mt2 ->
      reify_tm (app t1 t2) (mapp mt1 mt2)
| Reify_Abs :
    forall x t1 mt1,
      reify_tm t1 mt1 ->
      reify_tm (abs x t1) (mabs x mt1)
| Reify_Const :
    forall n, reify_tm (const n) (mconst n)
| Reify_Scc :
    forall t1 mt1,
      reify_tm t1 mt1 ->
      reify_tm (scc t1) (mscc mt1)
| Reify_Prd :
    forall t1 mt1,
      reify_tm t1 mt1 ->
      reify_tm (prd t1) (mprd mt1)    
| Reify_Test0 :
    forall t1 t2 t3 mt1 mt2 mt3,
      reify_tm t1 mt1 ->
      reify_tm t2 mt2 ->
      reify_tm t3 mt3 ->
      reify_tm (test0 t1 t2 t3) (mtest0 mt1 mt2 mt3)
| Reify_Unit :
    reify_tm unit munit
| Reify_Ref :
    forall t1 mt1,
      reify_tm t1 mt1 ->
      reify_tm (ref t1) (mref mt1)
| Reify_Deref :
    forall t1 mt1,
      reify_tm t1 mt1 ->
      reify_tm (deref t1) (mderef mt1)
| Reify_Assign :
    forall t1 t2 mt1 mt2,
      reify_tm t1 mt1 ->
      reify_tm t2 mt2 ->
      reify_tm (assign t1 t2) (massign mt1 mt2)
| Reify_Loc :
    forall l, reify_tm (loc l) (mloc l)
| Reify_Error :
    forall s, reify_tm (error s) (merror s).
Hint Constructors reify_tm.

Fixpoint reify_tm_fn (t : tm) : mtm :=
  match t with
  | var x' => mvar x'
  | app t1 t2 => mapp (reify_tm_fn t1) (reify_tm_fn t2)
  | abs x' t1 => mabs x' (reify_tm_fn t1)
  | const n => mconst n
  | scc t1 => mscc (reify_tm_fn t1)
  | prd t1 => mprd (reify_tm_fn t1)
  | test0 t1 t2 t3 => mtest0 (reify_tm_fn t1) (reify_tm_fn t2) (reify_tm_fn t3)
  | unit => munit
  | ref t1 => mref (reify_tm_fn t1)
  | deref t1  => mderef (reify_tm_fn t1)
  | assign t1 t2 => massign (reify_tm_fn t1) (reify_tm_fn t2)
  | loc l => mloc l
  | error s => merror s 
  end.

Theorem reify_tm_fn_sound :
  forall t mt,
    reify_tm t mt -> reify_tm_fn t = mt.
Proof.
  (* how to automate this proof?? it's pretty boilerplate-y *)
  intros t; induction t; intros; cbn; inversion H; subst; try reflexivity;
    try (specialize (IHt mt1); specialize (IHt H1); rewrite -> IHt; reflexivity).
  - specialize (IHt1 mt1). specialize (IHt1 H2). rewrite -> IHt1.
    specialize (IHt2 mt2). specialize (IHt2 H4). rewrite -> IHt2.
    reflexivity.
  - specialize (IHt mt1).  specialize (IHt H3).  rewrite -> IHt.
    reflexivity.
  - specialize (IHt1 mt1). specialize (IHt1 H3). rewrite -> IHt1.
    specialize (IHt2 mt2). specialize (IHt2 H5). rewrite -> IHt2.
    specialize (IHt3 mt3). specialize (IHt3 H6). rewrite -> IHt3.
    reflexivity.
  - specialize (IHt1 mt1). specialize (IHt1 H2). rewrite -> IHt1.
    specialize (IHt2 mt2). specialize (IHt2 H4). rewrite -> IHt2.
    reflexivity.
Qed.

(* think about the O here - how to make it general *)
Inductive reify_st : store -> mstore -> Prop :=
| ReifySt_Nil: reify_st [] []
| ReifySt_Cons:
    forall t mt s ms,
      reify_st s ms ->
      reify_tm t mt ->
      reify_st (t::s) ((mt, O)::ms).
Hint Constructors reify_st.

Definition reify_st_fn (st : store) : mstore :=
  map (fun t => (reify_tm_fn t, O)) st.

Theorem reify_st_fn_sound :
  forall s ms,
    reify_st s ms -> reify_st_fn s = ms.
Proof.
  intros s; induction s; intros; inversion H; subst.
  - reflexivity.
  - simpl.
    apply reify_tm_fn_sound in H4.
    specialize (IHs ms0).
    specialize (IHs H2).
    rewrite -> H4.
    rewrite -> IHs.
    reflexivity.
Qed.

Inductive reify : tm * store -> mtm * mstore -> Prop :=
| Reify : forall t s mt ms,
    reify_tm t mt ->
    reify_st s ms ->
    reify (t, s) (mt, ms).
Hint Constructors reify.

Definition reify_fn (t : tm) (st : store) : (mtm * mstore) :=
  (reify_tm_fn t, reify_st_fn st).
Hint Unfold reify_fn.

Theorem reify_fn_sound :
  forall t s mt ms mt' ms',
    reify (t, s) (mt, ms) -> reify_fn t s = (mt', ms') -> mt = mt' /\ ms = ms'.
Proof.
  intros.
  inversion H; subst.
  apply reify_tm_fn_sound in H4.
  apply reify_st_fn_sound in H6.
  inversion H0.
  split.
  - rewrite -> H4. reflexivity.
  - rewrite -> H6. reflexivity.
Qed.

Inductive reflect_mtm : mtm -> tm -> Prop :=
| Reflect_Var :
    forall x, reflect_mtm (mvar x) (var x)
| Reflect_App :
    forall mt1 mt2 t1 t2,
      reflect_mtm mt1 t1 -> reflect_mtm mt2 t2 ->
      reflect_mtm (mapp mt1 mt2) (app t1 t2)
| Reflect_Abs :
    forall x mt1 t1,
      reflect_mtm mt1 t1 ->
      reflect_mtm (mabs x mt1) (abs x t1)
| Reflect_Const :
    forall n, reflect_mtm (mconst n) (const n)
| Reflect_Scc :
    forall mt1 t1,
      reflect_mtm mt1 t1 ->
      reflect_mtm (mscc mt1) (scc t1)
| Reflect_Prd :
    forall t1 mt1,
      reflect_mtm mt1 t1 ->
      reflect_mtm (mprd mt1) (prd t1)    
| Reflect_Test0 :
    forall mt1 mt2 mt3 t1 t2 t3,
      reflect_mtm mt1 t1 ->
      reflect_mtm mt2 t2 ->
      reflect_mtm mt3 t3 ->
      reflect_mtm (mtest0 mt1 mt2 mt3) (test0 t1 t2 t3)
| Reflect_Unit :
    reflect_mtm munit unit
| Reflect_Ref :
    forall mt1 t1,
      reflect_mtm mt1 t1 ->
      reflect_mtm (mref mt1) (ref t1)
| Reflect_Deref :
    forall mt1 t1,
      reflect_mtm mt1 t1 ->
      reflect_mtm (mderef mt1) (deref t1)
| Reflect_Assign :
    forall mt1 mt2 t1 t2,
      reflect_mtm mt1 t1 ->
      reflect_mtm mt2 t2 ->
      reflect_mtm (massign mt1 mt2) (assign t1 t2)
| Reflect_Loc :
    forall l, reflect_mtm (mloc l) (loc l)
| Reflect_Error :
    forall s, reflect_mtm (merror s) (error s).
Hint Constructors reflect_mtm.

Fixpoint reflect_mtm_fn (mt : mtm) : tm :=
  match mt with
  | mvar x' => var x'
  | mapp t1 t2 => app (reflect_mtm_fn t1) (reflect_mtm_fn t2)
  | mabs x' t1 => abs x' (reflect_mtm_fn t1)
  | mconst n => const n
  | mscc t1 => scc (reflect_mtm_fn t1)
  | mprd t1 => prd (reflect_mtm_fn t1)
  | mtest0 t1 t2 t3 => test0 (reflect_mtm_fn t1) (reflect_mtm_fn t2) (reflect_mtm_fn t3)
  | munit => unit
  | mref t1 => ref (reflect_mtm_fn t1)
  | mderef t1 => deref (reflect_mtm_fn t1)
  | massign t1 t2 => assign (reflect_mtm_fn t1) (reflect_mtm_fn t2)
  | mloc l => loc l
  | merror s => error s 
  end.

Theorem reflect_mtm_fn_sound :
  forall mt t,
    reflect_mtm mt t -> reflect_mtm_fn mt = t.
Proof.
  (* how to automate this proof?? it's pretty boilerplate-y *)
  intros mt; induction mt; intros; cbn; inversion H; subst; try reflexivity;
    try (specialize (IHmt t1); specialize (IHmt H1); rewrite -> IHmt; reflexivity).
  - specialize (IHmt1 t1). specialize (IHmt1 H2). rewrite -> IHmt1.
    specialize (IHmt2 t2). specialize (IHmt2 H4). rewrite -> IHmt2.
    reflexivity.
  - specialize (IHmt t1).  specialize (IHmt H3).  rewrite -> IHmt.
    reflexivity.
  - specialize (IHmt1 t1). specialize (IHmt1 H3). rewrite -> IHmt1.
    specialize (IHmt2 t2). specialize (IHmt2 H5). rewrite -> IHmt2.
    specialize (IHmt3 t3). specialize (IHmt3 H6). rewrite -> IHmt3.
    reflexivity.
  - specialize (IHmt1 t1). specialize (IHmt1 H2). rewrite -> IHmt1.
    specialize (IHmt2 t2). specialize (IHmt2 H4). rewrite -> IHmt2.
    reflexivity.
Qed.

Inductive reflect_mst : mstore -> store -> Prop :=
| ReflectMst_Nil: reflect_mst [] []
| ReflectMst_Cons:
    forall mt t ms s n,
      reflect_mst ms s ->
      reflect_mtm mt t ->
      reflect_mst ((mt, n)::ms) (t::s).
Hint Constructors reflect_mst.

Definition reflect_mst_fn (mst : mstore) : store :=
  map (fun pair =>
         match pair with
         | (t, _) => reflect_mtm_fn t
         end)
      mst.

Theorem reflect_mst_fn_sound :
  forall ms s,
    reflect_mst ms s -> reflect_mst_fn ms = s.
Proof.
  intros s; induction s; intros; inversion H; subst.
  - auto.
  - simpl.
    apply reflect_mtm_fn_sound in H4.
    specialize (IHs s1).
    specialize (IHs H2).
    rewrite -> H4.
    rewrite -> IHs.
    reflexivity.
Qed.

Inductive reflect : mtm * mstore -> tm * store -> Prop :=
| Reflect :
    forall mt ms t s,
      reflect_mtm mt t ->
      reflect_mst ms s ->
      reflect (mt, ms) (t, s).
Hint Constructors reflect.

Definition reflect_fn (mt : mtm) (mst : mstore) : (tm * store) :=
  (reflect_mtm_fn mt, reflect_mst_fn mst).

Theorem reflect_fn_sound :
  forall mt ms t s t' s',
    reflect (mt, ms) (t, s) ->
    reflect_fn mt ms = (t', s') ->
    t = t' /\ s = s'.
Proof.
  intros.
  inversion H; subst.
  apply reflect_mtm_fn_sound in H4.
  apply reflect_mst_fn_sound in H6.
  inversion H0.
  split.
  - rewrite -> H4. reflexivity.
  - rewrite -> H6. reflexivity.
Qed.

Lemma reify_reflect_inv_t :
  forall t s mt ms ms' t' s',
    reify (t, s) (mt, ms) ->
    reflect (mt, ms') (t', s') ->
    t = t'.
Proof.
  intros t; induction t; intros;
  inversion H ; subst; inversion H0; subst; inversion H4; subst;
  inversion H5; subst; inversion H6; subst; inversion H8; subst;
    eauto;
    try (assert (t = t1) as TT1 by eauto;
         rewrite TT1; reflexivity);
    try (assert (t1 = t0) as T1T0 by eauto;
         assert (t2 = t3) as T2T3 by eauto;
         rewrite T1T0; rewrite T2T3; reflexivity);
    try (assert (t1 = t0) as T1T0 by eauto;
         assert (t2 = t4) as T2T4 by eauto;
         assert (t3 = t5) as T3T5 by eauto;
         rewrite T1T0; rewrite T2T4; rewrite T3T5; reflexivity).
Qed.

Lemma reify_st_reflect_mst_inv :
  forall s ms s',
    reify_st s ms ->
    reflect_mst ms s' ->
    s = s'.
Proof.
  intros s; induction s; intros.
  inversion H; subst; inversion H0; subst; auto.
  inversion H; subst. inversion H0; subst.
  assert (a = t) by eauto using reify_reflect_inv_t. rewrite H1.
  specialize (IHs ms0 s0 H3 H7). rewrite IHs.
  auto.
Qed.

Lemma reify_reflect_inv_s :
  forall t s mt mt' ms t' s',
    reify (t, s) (mt, ms) ->
    reflect (mt', ms) (t', s') ->
    s = s'.
Proof.
  intros.
  inversion H; subst; inversion H0; subst.
  generalize H8. generalize H6.
  apply reify_st_reflect_mst_inv.
Qed.

Lemma reify_reflect_inv :
  forall t s mt ms t' s',
    reify (t, s) (mt, ms) ->
    reflect (mt, ms) (t', s') ->
    t = t' /\ s = s'.
Proof.
  intros. split.
  - eauto using reify_reflect_inv_t.
  - eauto using reify_reflect_inv_s.
Qed.

Ltac invsubst x := inversion x; subst.

Ltac pinvsubst x := idtac x; invsubst x.

Ltac invert_something :=
  match goal with
  | [ H : metastep _ _ |- _] => pinvsubst H
  | [ H : reify _ _ |- _] => pinvsubst H
  | [ H : reflect _ _ |- _] => pinvsubst H
  | [ H : reify_tm _ _ |- _] => pinvsubst H
  | [ H : reify_st _ _ |- _] => pinvsubst H
  | [ H : reflect_mtm _ _ |- _] => pinvsubst H
  | [ H : reflect_mst _ _ |- _] => pinvsubst H
  | _ => idtac
  end.

Ltac invert_all := repeat (try (progress invert_something)).

Lemma reify_preserves_values :
  forall t mt,
    reify_tm t mt ->
    value t -> mvalue mt.
Proof.
  intros t mt R V; invsubst V; invsubst R; eauto.
Qed.

Lemma reify_preserves_mvalues :
  forall t mt,
    reify_tm t mt -> mvalue mt -> value t.
Proof.
  - intros t mt R MV; invsubst MV; invsubst R; eauto.
Qed.

Lemma mvalue_not_metastep :
  forall mt ms,
    mvalue mt ->
    ~ (exists mt' ms', mt / ms -m> mt' / ms').
Proof.
  intros; inversion H; intuition; inversion H1; inversion H2; inversion H3.
Qed.  

Theorem reflection_sound :
  forall t s t' s' mt ms mt' ms' t'' s'',
    t / s --> t' / s' ->
    reify (t, s) (mt, ms) ->
    mt / ms -m> mt' / ms' ->
    reflect (mt', ms') (t'', s'') ->
    t' = t'' /\ s' = s''.
Proof.
  intros t.
  induction t; intros; invsubst H; simpl.
  - invsubst H0. invsubst H7. invsubst H6.
    assert (mvalue mt2) by eauto using reify_preserves_values.
    assert (mvalue (mabs x mt0)) by eauto.
    invsubst H1.
    + admit. 
    + invsubst H12.
    + exfalso. specialize (mvalue_not_metastep mt2 ms H3). intuition.
      apply H8. exists t2'. exists ms'. exact H17.
  - admit.
  - admit.
  - invsubst H0. invsubst H6. invsubst H1.
    + invsubst H2. invsubst H9. invsubst H4. intuition.
      eapply reify_reflect_inv_s; eauto.
    + invsubst H0. invsubst H10. invsubst H9.
      invsubst H5.
  - invsubst H0.
    invsubst H7.
    assert (~value t) by eauto using step_not_value.
    assert (~ mvalue mt1) by eauto using reify_preserves_mvalues.
    
    specialize (IHt s t1' s' ).
    assert (reify (t, s) (mt1, ms)) by eauto.    
    
    
       


