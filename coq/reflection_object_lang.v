From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Decidable.
Import ListNotations.

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
  | reflect : tm -> store -> tm
with store :=
  | STORE : list tm -> store.


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
  | reflect _ _ => t
  end.
Notation "'[' x ':=' s ']' t" := (subst x s t) (at level 20).


(* equivalent to `t1; t2` *)
Definition tseq t1 t2 :=
  app (abs "x" t2) t1.


(* store-based substitution semantics *)

Definition store_lookup (n:nat) (st:store) :=
  match st with
  | STORE l => nth n l unit
  end.

Fixpoint replace {A:Type} (n:nat) (x:A) (l:list A) : list A :=
  match l with
  | nil => nil
  | h :: t =>
    match n with
    | O => x :: t
    | S n' => h :: replace n' x t
    end
  end.

Definition store_replace n x st :=
  match st with
  | STORE l => STORE (replace n x l)
  end.

Definition st_length st :=
  match st with
  | STORE l => length l
  end.

Definition st_append v st :=
  match st with
  | STORE l => STORE (l ++ (v::nil))
  end.

Reserved Notation "t1 '/' st1 '-->' t2 '/' st2"
  (at level 40, st1 at level 39, t2 at level 39).

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
         ref v1 / st --> loc (st_length st) / (st_append v1 st)
  | ST_Ref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         ref t1 /  st --> ref t1' /  st'
  | ST_DerefLoc : forall st l,
         l < st_length st ->
         deref (loc l) / st --> store_lookup l st / st
  | ST_Deref : forall t1 t1' st st',
         t1 / st --> t1' / st' ->
         deref t1 / st --> deref t1' / st'
  | ST_Assign : forall v2 l st,
         value v2 ->
         l < st_length st ->
         assign (loc l) v2 / st --> unit / store_replace l v2 st
  | ST_Assign1 : forall t1 t1' t2 st st',
         t1 / st --> t1' / st' ->
         assign t1 t2 / st --> assign t1' t2 / st'
  | ST_Assign2 : forall v1 t2 t2' st st',
         value v1 ->
         t2 / st --> t2' / st' ->
         assign v1 t2 / st --> assign v1 t2' / st'
  | ST_Reflect : forall t st st',
      reflect t st / st'  --> t / st
where "t1 '/' st1 '-->' t2 '/' st2" := (step (t1,st1) (t2,st2)).
Hint Constructors step.




(* 

reify - take current continuation as argument


reflect - replace current continuation with argument

*)
