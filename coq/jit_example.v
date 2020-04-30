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
  | test0_speculate_then : tm -> tm -> tm -> tm
  | test0_speculate_else : tm -> tm -> tm -> tm
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
  | test0_speculate_then t1 t2 t3 =>
      test0_speculate_then (subst x s t1) (subst x s t2) (subst x s t3)
  | test0_speculate_else t1 t2 t3 =>
      test0_speculate_else (subst x s t1) (subst x s t2) (subst x s t3)
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

Definition config : Type := tm * store.

Reserved Notation "t1 '/' st1 '-->' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

Inductive step : config -> config -> Prop :=
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
  | ST_If0_SpecThen : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         test0_speculate_then t1 t2 t3 / st -->
           test0_speculate_then t1' t2 t3 / st'
  | ST_If0_Zero_SpecThen : forall t2 t3 st,
         test0_speculate_then (const 0) t2 t3 / st --> t2 / st
  | ST_If0_Nonzero_SpecThen : forall n t2 t3 st,
      test0_speculate_then (const (S n)) t2 t3 / st --> t3 / st
  | ST_If0_SpecElse : forall t1 t1' t2 t3 st st',
         t1 / st --> t1' / st' ->
         test0_speculate_else t1 t2 t3 / st -->
           test0_speculate_else t1' t2 t3 / st'
  | ST_If0_Zero_SpecElse : forall t2 t3 st,
         test0_speculate_else (const 0) t2 t3 / st --> t2 / st
  | ST_If0_Nonzero_SpecElse : forall n t2 t3 st,
         test0_speculate_else (const (S n)) t2 t3 / st --> t3 / st
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


Fixpoint stepfn' (t : tm) (s : store) : config :=
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
        let (arg',s') := stepfn' arg s in
        (app fn arg', s')
    else
      let (fn',s') := stepfn' fn s in
      (app fn' arg, s')
  | scc t1 =>
    if (valueb t1) then
      match t1 with
      | const n => (const (S n), s)
      | _ => (error "scc of non nat", s)
      end
    else
      let (t1', s') := stepfn' t1 s in
      (scc t1', s')
  | prd t1 =>
    if (valueb t1) then
      match t1 with
      | const n => (const (pred n), s)
      | _ => (error "prd of non nat", s)
      end
    else
      let (t1', s') := stepfn' t1 s in
      (prd t1', s')
  | test0 cond yes no =>
    if (valueb cond) then
      match cond with
      | const 0 => (yes, s)
      | const (S n) => (no, s)
      | _ => (error "test0 of non nat", s)
      end
    else
      let (cond', s') := stepfn' cond s in
      (test0 cond' yes no, s')
  | test0_speculate_then cond yes no =>
    if (valueb cond) then
      match cond with
      | const 0 => (yes, s)
      | const (S n) => (no, s)
      | _ => (error "test0_speculate_then of non nat", s)
      end
    else
      let (cond', s') := stepfn' cond s in
      (test0_speculate_then cond' yes no, s')
  | test0_speculate_else cond yes no =>
    if (valueb cond) then
      match cond with
      | const 0 => (yes, s)
      | const (S n) => (no, s)
      | _ => (error "test0_speculate_else of non nat", s)
      end
    else
      let (cond', s') := stepfn' cond s in
      (test0_speculate_else cond' yes no, s')
  | ref t1 =>
    if (valueb t1) then
      (loc (length s), (s ++ t1::nil))
    else
      let (t1', s') := stepfn' t1 s in
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
      let (t1', s') := stepfn' t1 s in
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
        let (t2', s') := stepfn' t2 s in
        (assign t1 t2', s')
    else
      let (t1', s') := stepfn' t1 s in
      (assign t1' t2, s')   
  end.
Hint Unfold stepfn'.

Definition stepfn (c : config) : config :=
  let (t, s) := c in stepfn' t s.
Hint Unfold stepfn.

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
  | _ => idtac
  end.

Ltac stepfn_sound_tac4 :=
  match goal with
  | [ H : (forall _ _ _, (?t / _ --> _ / _) -> _),
      H1 : ?t / ?s --> ?t' / ?s' |- _] =>
    specialize (H s t' s' H1); now rewrite H
  | [ H : (forall _ _ _, (?t / _ --> _ / _) -> _) |- _ ] => auto
  | _ => idtac
  end.
                                       
Ltac stepfn_sound_tac :=
  stepfn_sound_tac1; stepfn_sound_tac2;
  stepfn_sound_tac3; stepfn_sound_tac4.

Theorem stepfn_sound : forall t1 s1 t2 s2,
    t1 / s1 --> t2 / s2 -> stepfn (t1, s1) = (t2, s2).
Proof.
  induction t1; intros s1 t2 s2 H;
    inversion H; subst; simpl;
    unfold stepfn in *;
    stepfn_sound_tac.
  - apply Nat.ltb_lt in H1. now rewrite H1.
  - apply Nat.ltb_lt in H6. now rewrite H6.
Qed.


Module MemoryInstrumentationMeta.

(* count number of memory operations at each memory address *)
Definition metainfo : Type := list nat.

Definition metaconfig : Type := config * metainfo.

Definition reify (c : config) : metaconfig :=
  let (_, s) := c in (c, List.repeat 0 (length s)).

(* Import ListNotations. *)
(* Definition store1 := cons (const 1) *)
(*                           (cons (const 2) *)
(*                                 (cons (const 3) *)
(*                                       nil)). *)
(* Compute (reify (var "x", store1)). *)

Definition reflect (mc : metaconfig) : config :=
  let (c, _) := mc in c.

Fixpoint incr_loc (n : nat) (l : metainfo) : metainfo :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => (S h) :: t
    | S n' => h :: incr_loc n' t
    end
  end.

Definition infostepfn (mc : metaconfig) : metainfo :=
  let (c, mi) := mc in
  let (t,  _) :=  c in
  match t with
  | ref t' => if valueb t' then mi ++ (0 :: nil) else mi
  | deref (loc l) | assign (loc l) _ =>
    if Nat.ltb l (length mi) then incr_loc l mi else nil (* error *)
  | _ => mi
  end.

Definition configstepfn (mc : metaconfig) : config :=
  let (c, _) := mc in stepfn c.

Definition metastepfn (mc : metaconfig) : metaconfig :=
  (configstepfn mc, infostepfn mc).

Theorem reflection_sound :
  forall c c',
    step c c' ->
    reflect (metastepfn (reify c)) = c'.
Proof.
  intros. cbn. destruct c. destruct c'.
  unfold configstepfn in *. cbn.
  eauto using stepfn_sound.
Qed.     

End MemoryInstrumentationMeta.
  

Module JitMeta.
  (* TODO: try to express speculate in the object lang? *)

  Definition let_tm (s : string) (t1 : tm) (t2 : tm) :=
    app (abs s t2) t1.

  (* need a better way of dealing with counters *)
  Definition instrument (t : tm) (then_ctr : string) (else_ctr : string) : tm :=
    match t with
    | test0 cond yes no =>
      (* let_tm then_ctr (ref (const 0)) *)
      (*        (let_tm else_ctr (ref (const 0)) *)
      test0 cond
            (tseq (assign (var then_ctr) (scc (deref (var then_ctr))))
                  yes)
            (tseq (assign (var else_ctr) (scc (deref (var else_ctr))))
                  no)                          
    | _ => t
    end.



  Definition counter_value (c : config) (ctr : string) : nat :=
    let (_, s) := c in
    match stepfn (deref (var ctr), s) with
    | (const n, _) => n
    | _ => 0 (* error *)
    end.
             
  Definition speculate (c : config) (then_ctr : string) (else_ctr : string) : config :=
    let (t, s) := c in
    match t with
    | test0 cond yes no =>
      let then_ct := counter_value c then_ctr in
      let else_ct := counter_value c else_ctr in
      if (Nat.ltb else_ct then_ct) then
        (test0_speculate_then cond yes no, s)
      else
        (test0_speculate_else cond yes no, s)
    | _ => c
    end.
  
  
End JitMeta.
