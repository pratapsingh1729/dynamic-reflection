(* Andrzej Filinski. 1999. Representing layered monads. 
 * In Proceedings of the 26th ACM SIGPLAN-SIGACT symposium 
 * on Principles of programming languages (POPL ’99). 
 * Association for Computing Machinery, New York, NY, USA, 175–188. 
 * DOI:https://doi.org/10.1145/292540.292557 *)

(* ------------------------------------------------------------------ *)
(* Figure 2: Representing continuation-passing with escapes and state *)

abstype void = VOID of void
with fun coerce (VOID v) = coerce v
end;

signature ESCAPE =
sig
  val escape : (('a -> void) -> void) -> 'a
end;

structure Escape0 : ESCAPE =
struct
  fun escape h =
    SMLofNJ.Cont.callcc (fn k => 
      coerce (h (fn x => SMLofNJ.Cont.throw k x)))
end;

signature CTRL = 
sig
  type ans
  val shift : (('a -> ans) -> ans) -> 'a
  val reset : (unit -> ans) -> ans
  include ESCAPE
end;

functor RepCPS (type ans
                structure E : ESCAPE) :
    CTRL where type ans = ans =
struct
  type ans = ans
  fun initmk a = raise Fail "Unexpected control effect"
  val mk = ref (initmk : ans -> void)

  fun abort v = !mk v
  fun reset t =
    E.escape (fn k =>
      let val m = !mk 
      in mk := (fn a => (mk := m; k a));
          abort (t ())
      end)
  fun shift h = 
    E.escape (fn k =>
      abort (h (fn v =>
                  reset (fn () => coerce (k v)))))

  fun escape h = 
    E.escape (fn k =>
      let val m = !mk
      in mk := initmk; h (fn a => (mk := m; k a)) end)
end;


(* ------------------------------------------------------------- *)
(* Figure 3: A universal type, with a state-based implementation *)

signature DYNAMIC =
sig 
  exception Dynamic
  type dyn
  val newdyn : unit -> ('a -> dyn) * (dyn -> 'a)
end;

structure Dynamic :> DYNAMIC =
struct
  exception Dynamic
  datatype dyn = DYN of unit -> unit
  fun newdyn () = 
    let val r = ref NONE
    in (fn a => DYN (fn () => r := SOME a),
        fn (DYN d) =>
          (r := NONE; d (); 
           case !r of SOME a => a
                    | NONE   => raise Dynamic))
    end
end;

(* ---------------------------------------------------------------- *)
(* Figure 4: Representing monadic effects with continuation-passing *)

signature MONAD =
sig
  type 'a t
  val unit : 'a -> 'a t
  val bind : 'a t * ('a -> 'b t) -> 'b t
  val glue : (unit -> 'a t) -> 'a t
  val show : string t -> string
end;

signature RMONAD =
sig
  structure M : MONAD
  val reflect : 'a M.t -> 'a
  val reify : (unit -> 'a) -> 'a M.t
end;

signature EFFREP =
sig
  include ESCAPE
  val run : (unit -> string) -> string
end;

structure Eff0: EFFREP =
struct
  open Escape0
  fun run t = t ()
end;

functor Represent (structure M : MONAD
                   structure E : EFFREP) :
  sig include RMONAD include EFFREP end =
struct 
  structure C = RepCPS (type ans = Dynamic.dyn M.t
                        structure E = E)
  structure M = M
  fun reflect m =
    C.shift (fn k =>
      M.bind (m, fn a => M.glue (fn () => k a)))
  fun reify t = 
    let val (in_d, out_d) = Dynamic.newdyn ()
    in M.glue (fn () =>
          M.bind (C.reset (fn () =>
                      M.unit (in_d (t ()))),
                  M.unit o out_d))
    end
  val escape = C.escape
  fun run t = M.show (reify (fn () => E.run t))
end;

(* ------------------------------------------------- *)
(* Figure 5: Some simple monads and their operations *)

structure Exceptions =
struct
  datatype 'a res = OK of 'a | EXN of string
  type 'a t = unit -> 'a res
  fun glue t = fn () => t () ()
  fun unit a = fn () => OK a
  fun bind (t, f) =
    fn () => case t () of OK a => f a () | EXN s => EXN s
  fun show t = 
    case t () of OK s => s | EXN x => "<exn: " ^ x ^ ">"
end;

functor ExceptionOps (structure R : RMONAD where M = Exceptions) :
  sig
    val fraise : string -> 'a
    val fhandle : (unit -> 'a) -> (string -> 'a) -> 'a
  end =
struct
  open Exceptions
  fun fraise s = R.reflect (fn () => EXN s)
  fun fhandle t h =
    case R.reify t () of OK a => a | EXN s => h s 
end;

structure State : MONAD =
struct
  type state = int
  type 'a t = state -> 'a * state
  fun glue t = fn s => t () s
  fun unit a = fn s => (a, s)
  fun bind (t, f) =
    fn s => let val (a,s') = t s in f a s' end
  fun show t = 
    let val (a, s) = t 0
    in if s = 0 then a
                else "<st: " ^ Int.toString s ^ ">" ^a
    end
end;

functor StateOps (structure R : RMONAD where M = State) :
  sig
    val get : unit -> int
    val set : int -> unit
  end =
struct
  fun get () = R.reflect (fn s => (s, s))
  fun set n = R.reflect (fn s => ((), n))
end;

structure ListMonad : MONAD =
struct
  type 'a t = unit -> 'a list
  fun glue t = fn () => t () ()
  fun unit a = fn () => [a]
  fun mapcan f [] = []
    | mapcan f (h::t) = f h @ mapcan f t
  fun bind (t, f) =
    fn () => mapcan (fn a => f a ()) (t ())
  
  fun disp [] = "<fail>"
    | disp [x] = x
    | disp (h::t) = h ^ " <or> " ^ disp t
  fun show t = disp (t ())
end;

(* --------------------------------- *)
(* Section 4.1: Exceptions and state *)

structure E = Eff0;
structure E = Represent(structure M = Exceptions
                        structure E = E); 
structure Rex = E;
structure ExcOps = ExceptionOps(structure R = Rex);
structure E = Represent (structure M = State
                         structure E = E);
structure Rst = E;
structure StateOps= StateOps(structure R = Rst);

val t1 = E.run (fn () => (StateOps.set 3; "ok"));
(* val t1 = "<st: 3>ok" : string *)
val t2 = E.run (fn () => (StateOps.set 4; ExcOps.fraise "err"; "ok"));
(* val t2 = "<st: 4><exn: err>" : string *)
val t3 = E.run (fn () =>
            (StateOps.set 5;
             ExcOps.fhandle
              (fn () => (StateOps.set 8;
                         ExcOps.fraise "err"; "ok"))
              (fn x => x ^ ", " ^
                  Int.toString (StateOps.get ()))));
(* val t3 = "<st: 8>err, 8" : string *)

(* ---------------------------------------------------- *)
(* Figure 6: Resumption monad and associated operations *)

structure Resumptions =
struct
  datatype 'a res = DONE of 'a | SUSP of 'a t
  withtype 'a t = unit -> 'a res
  fun glue t = fn () => t () ()
  fun unit a = fn () => DONE a
  fun step (DONE a, f) = f a ()
    | step (SUSP t, f) = SUSP (bind (t, f))
  and bind (t, f) = fn () => step (t (), f)
  fun disp (DONE a) = a
    | disp (SUSP t) = show t
  and show t = disp (t ())
end;

functor ParallelOps (structure R : 
                        RMONAD where M = Resumptions) :
  sig
    val yield : unit -> unit
    val por : (unit -> bool) * (unit -> bool) -> bool
  end =
struct 
  open Resumptions
  fun yield () = R.reflect (fn () => SUSP (unit ()))
  fun por (t1, t2) =
    let fun step (DONE true, _) = DONE true
          | step (DONE false, p) = p ()
          | step (SUSP t1, t2) = SUSP (rpor (t2, t1))
        and rpor (t1, t2) () = step (t1 (), t2)
    in R.reflect (rpor (R.reify t1, R.reify t2)) 
    end
end;

functor ConcurOps (structure RR : RMONAD where M = Resumptions
                   structure RL : RMONAD where M = ListMonad) :
  sig
    val par : (unit -> 'a) * (unit -> 'b) -> 'a * 'b
    val atomically : (unit -> 'a) -> 'a
  end =
struct
  open Resumptions
  fun atomically t =
    let fun step (DONE a, y) = if y then SUSP (unit a) else DONE a
          | step (SUSP t, y) = step (t (), true)
        and atom t () = step (t (), false)
    in RR.reflect (atom (RR.reify t)) 
    end
  fun par (t1, t2) =
    let fun step (DONE a, DONE b) = DONE (a,b)
          | step (DONE a, SUSP tb) = SUSP (bind (tb, fn b => unit (a,b)))
          | step (SUSP ta, DONE b) = SUSP (bind (ta, fn a => unit (a,b)))
          | step (SUSP ta, SUSP tb) = SUSP (rpar (ta, tb))
        and rpar (t1, t2) () =
          if RL.reflect (fn () => [true, false])
          then step (t1 (), SUSP t2)
          else step (SUSP t1, t2 ())
    in RR.reflect (rpar (RR.reify t1, RR.reify t2))
    end
end;

(* ------------------------------------- *)
(* Section 4.2: Shared-state concurrency *)

structure E = Eff0;
structure E = Represent (structure E = E structure M = Resumptions)
structure Rrs = E
structure ParOps = ParallelOps (structure R = Rrs)
structure E = Represent (structure E = E structure M = State)
structure Rst = E
structure Cell = StateOps (structure R = Rst);
structure E = Represent (structure E = E structure M = ListMonad)
structure Rls = E
structure Conc = ConcurOps (structure RR = Rrs structure RL = Rls)

structure Shared = 
struct
  fun store n = (ParOps.yield (); Cell.set n)
  fun fetch () = (ParOps.yield (); Cell.get ())
end;

val t1 = E.run (fn () =>
            (Conc.par (fn () => Shared.store 3,
                       fn () => Shared.store
                                    (Shared.fetch () + 1));
             Int.toString (Shared.fetch ())));

val t2 = E.run (fn () =>
            (Conc.par (fn () => Shared.store 3,
                       fn () => Conc.atomically 
                                  (fn () => Shared.store (Shared.fetch () + 1)));
             Int.toString (Shared.fetch ())));





