From Coq Require Import Strings.String.
From Coq Require Import Arith.Arith.
From Coq Require Import omega.Omega.
From Coq Require Import Lists.List.
From Coq Require Import Decidable.
Import ListNotations.

(* a continuation-based semantics for an IMP-like language, loosely based on
 * https://xavierleroy.org/courses/EUTypes-2019/html/EUTypes2019.CompilerVerification.IMP.html *)

Definition ident := string.
Definition store : Type := ident -> nat.

(* large-step for arithmetic expressions *)
Inductive aexp : Type :=
  | aconst (n: nat)                       
  | avar (x: ident)                     
  | aplus (a1: aexp) (a2: aexp)
  | amult (a1 : aexp) (a2: aexp).

Fixpoint aeval (s: store) (a: aexp) : nat :=
  match a with
  | aconst n => n
  | avar x => s x
  | aplus a1 a2 => aeval s a1 + aeval s a2
  | amult a1 a2 => aeval s a1 * aeval s a2
  end.
Hint Unfold aeval.

(* large-step for boolean expressions *)
Inductive bexp : Type :=
  | btrue | bfalse
  | beq (a1: aexp) (a2: aexp)       
  | bleq (a1: aexp) (a2: aexp)   
  | bnot (b1: bexp)                    
  | band (b1: bexp) (b2: bexp)
  | bor  (b1: bexp) (b2: bexp).

Fixpoint beval (s: store) (b: bexp) : bool :=
  match b with
  | btrue => true
  | bfalse => false
  | beq a1 a2 => aeval s a1 =? aeval s a2
  | bleq a1 a2 => aeval s a1 <=? aeval s a2
  | bnot b1 => negb (beval s b1)
  | band b1 b2 => beval s b1 && beval s b2
  | bor b1 b2 => beval s b1 || beval s b2
  end.
Hint Unfold beval.

(* statements and continuations in the language *)
Inductive stmt : Type :=
  | skip : stmt
  | assign : ident -> aexp -> stmt       
  | seq : stmt -> stmt -> stmt         
  | cond : bexp -> stmt -> stmt -> stmt
  | while : bexp -> stmt -> stmt
  | reify : cont -> stmt (* jump to this new continuation, with the old continuation and store added to the full store *)
  | reflect : stmt  (* reflect whatever is in the old continuation and store into the running process *)
with cont :=
  | CONT : list stmt -> cont.

(* TODO add constructs to manipulate the reified continuation and store *)


Definition store_empty : store := fun (s : ident) => 0. (* TODO clean this up using options or PartialMap *)
  
Definition store_update (x: ident) (v: nat) (s: store) : store :=
  fun y => if string_dec x y then v else s y.

Definition full_store : Type := store * cont * store. (* program store, reified continuation, reified store *)

Inductive step: stmt * cont * full_store -> stmt * cont * full_store -> Prop :=
  | step_assign: forall x a k s rk rs,              
      step (assign x a, CONT k, (s, rk, rs)) (skip, CONT k, (store_update x (aeval s a) s, rk, rs))
  | step_seq: forall c1 c2 s k rk rs,               
      step (seq c1 c2, CONT k, (s, rk, rs)) (c1, CONT (c2 :: k), (s, rk, rs))
  | step_cond: forall b c1 c2 k s rk rs,
      step (cond b c1 c2, CONT k, (s, rk, rs)) ((if beval s b then c1 else c2), CONT k, (s, rk, rs))
  | step_while_done: forall b c k s rk rs,
      beval s b = false ->
      step (while b c, CONT k, (s, rk, rs)) (skip, CONT k, (s, rk, rs))
  | step_while_true: forall b c k s rk rs,
      beval s b = true ->
      step (while b c, CONT k, (s, rk, rs)) (c, CONT (while b c :: k), (s, rk, rs))
  | step_skip_seq: forall c k s rk rs,
      step (skip, CONT (c :: k), (s, rk, rs)) (c, CONT k, (s, rk, rs))
  | step_reify: forall newk k s rk rs,
      step (reify newk, CONT k, (s, rk, rs)) (skip, newk, (store_empty, CONT k, s))
  | step_reflect: forall k s rk rs,
      step (reflect, CONT k, (s, rk, rs)) (skip, rk, (rs, CONT (@nil stmt), store_empty)).
Hint Constructors step.


(* 

programs in this language would look something like this:
reify { 
      <statements to do whatever processing we want>;
      reflect
}
< code to be reified >

*)
