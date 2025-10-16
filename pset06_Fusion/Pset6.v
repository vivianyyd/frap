(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 6 *)
Require Import Frap.Frap Pset6.Pset6Sig.
Import Swap.
(*|
Modern compilers achieve excellent performance by leveraging a wide variety of
program transformations.  For example, GCC (the GNU C compiler) version 10.2
produces the *exact same* assembly code for the following two programs (if you
want to see for yourself, try it on https://godbolt.org!):

1. Recursive version with accumulator, naive division and modulo, no function
   inlining, multiple returns, redundant ``+ 1``, not tail-recursive::

      static unsigned int affine(unsigned int n,
                                 unsigned int slope,
                                 unsigned int offset) {
          return n * slope + offset;
      }

      unsigned int collatz1(unsigned int start) {
          if (start == 1)
            return 0;
          else if (start % 2 == 0)
            return collatz1(start / 2) + 1;
          else
            return collatz1(affine(start, 3, 1)) + 1;
      }

2. Single loop, inlined function, bitwise arithmetic::

      unsigned int collatz2(unsigned int start) {
          unsigned int flight = 0;
          while (start != 1) {
              flight++;
              if ((start & 1) == 0) {
                  start = start >> 1;
              } else {
                  start = start * 2 + start + 1;
              }
          }
          return flight;
      }

The way GCC achieves this is by applying a sequence of transformation passes on
the code: you can see the output of each intermediate pass (all ~320 of them)
using ``gcc -O3 -fdump-tree-all -fdump-rtl-all -c collatz1.c``.  For instance,
the ``ssa`` pass puts the code into a form similar to the three-address code
that we saw in class, the ``tailr1`` passes convert the recursive function to a
loop, etc.

Students interested in an introduction to the magic of modern compiler
optimizations might enjoy Matt Godbolt's 2017 talk at CPPCon, *What Has My
Compiler Done for Me Lately? Unbolting the Compiler's Lid*
(https://www.youtube.com/watch?v=bSkpMdDe4g4).

In this lab, we'll see how formal methods can help us reason about the
correctness of these optimization passes, focusing on a couple of particular
optimizations.

Pset6Sig.v contains the number of points you get for each definition and
proof. Note that since we ask you to come up with some definitions
yourself, all proofs being accepted by Rocq does not necessarily guarantee a
full score: you also need to make sure that your definitions correspond to
what we ask for in the instructions. That said, if the required tests pass
and your definitions do not intentionally special-case them, you should be
fine.

*A few notes of caution*:

- Some of the proofs in this lab can be a bit long to complete fully manually:
  we encourage you to try your hand at simple automation.  However, make sure
  that your whole file compiles in a reasonable amount of time (at most a minute
  or two).

- When decomposed into the right sequence of lemmas, most of the theorems in
  this pset have relatively short proofs.  The best way to find these lemmas is
  to approach each problem cautiously, trying to work an understanding of the
  proof before diving into long series of `invert`, `econstructor`, etc.  In
  general, it's also a good idea to admit lemmas until you are sure that they
  allow you to prove the complete theorem, then go back and prove the lemmas —
  but do take the time to convince yourself that your lemmas make sense, so that
  you don't waste time using incorrect lemmas.

- We have included plenty of hints below in the HINTS section of the 
  signature file.
|*)

Module Impl.

(*
  We'll be working with a small stack-based language in this lab, where we
  interpret a program as a transformation from an input stack to an output stack,
  primarily done by pushing and popping values on and off the stack.
 *)

(*
  Our values consist of natural numbers and lists of values.
  So that we can have a single value type, we use the following datatype:
 *)
Inductive stack_val :=
| val_lit (n : nat)
| val_nil
| val_cons (v1 v2 : stack_val).

(*
  However, this inductive definition admits expressions that do not conform
  to our English definition of our set of values. For example, the following
  term has the Rocq type `stack_val`: `val_cons (val_lit 0) (val_lit 1)`, even
  though we see it as ill-formed since the tail of a cons should be a list.
  In order to describe the set of well-formed values, we define the following
  datatype of stack-language type signatures and an associated typing judgment
  for stack values.

  The typing judgments in this lab are fairly straightforward since they only
  have to be concerned with natural numbers and lists, but you can think of them
  as a preview of the sort of problems that will be in next week's assignment.
 *)
Inductive ty : Set :=
| ty_nat
| ty_list (t : ty).

Inductive val_well_typed : stack_val -> ty -> Prop :=
| val_lit_wt n : val_well_typed (val_lit n) ty_nat
| val_nil_wt t : val_well_typed val_nil (ty_list t)
| val_cons_wt t v1 v2
  : val_well_typed v1 t ->
      val_well_typed v2 (ty_list t) ->
      val_well_typed (val_cons v1 v2) (ty_list t).
Local Hint Constructors val_well_typed : core.

(* Since a stack is a list of values, we can use this judgment to define
  a typing judgment for stacks as well. The type of a stack is just a list
  of the types of its values. Since `val_well_typed` is a binary relation,
  we can use `Forall2` from the standard library to lift it to operate on stacks.
  You can see the definition of `Forall2` by printing it: *)
Print Forall2.

(* We define `stack_well_typed` as a notation instead of a definition for some
  convenience in tactics. You don't need to pay attention to the difference
  except to know that you can't unfold `stack_well_typed`, but Rocq automatically
  will see it as a use of `Forall2`. *)
Notation stack_well_typed := (Forall2 val_well_typed).
Local Hint Constructors Forall2 : core.

(* Here are some definitions that we will use in the interpreter.
   Many of them have dummy cases that we do not expect to hit.
   Specifically, the benefit of all of the typing judgments is that
   they guarantee these cases will never happen. *)
Definition stack_unop f (s : list stack_val) :=
  match s with
  | a::s' => (f a)::s'
  | _ => (*this case never happens on well-typed programs*) s
  end.

Definition stack_binop f (s : list stack_val) :=
  match s with
  | a::b::s' => (f a b)::s'
  | _ => (*this case never happens on well-typed programs*) s
  end.

Definition stack_pop (s : list stack_val) :=
  match s with
  | a::s => (a,s)
  | _ => (*this case never happens on well-typed programs*) (val_lit 0, [])
  end.

Definition stack_peek (s : list stack_val) :=
  match s with
  | a::_ => a
  | _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Fixpoint val_app v1 v2 :=
  match v1 with
  | val_nil => v2
  | val_cons v11 v12 => val_cons v11 (val_app v12 v2)
  | val_lit _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Fixpoint val_flatmap (f : stack_val -> stack_val) v :=
  match v with
  | val_nil => val_nil
  | val_cons v1 v2 =>
      val_app (f v1) (val_flatmap f v2)
  | val_lit _ => val_lit 0
  end.

Fixpoint val_reduce (f : stack_val -> stack_val -> stack_val) vl vacc :=
  match vl with
  | val_nil => vacc
  | val_cons v1 v2 =>
      val_reduce f v2 (f vacc v1)
  | val_lit _ => val_lit 0
  end.

(*
  You will have to prove some lemmas about most of these functions to finish
  the later exercises. We've given you one of the more complicated ones here
  to prove, but you should come up with your own for the other functions as
  needed.
 *)

Lemma app_well_typed v1 v2 t
  : val_well_typed v1 (ty_list t) ->
    val_well_typed v2 (ty_list t) ->
    val_well_typed (val_app v1 v2) (ty_list t).
Proof.
  simplify. induct v1; simpl.
  - invert H. 
  - trivial.
  - invert H. eauto. 
Qed.

Lemma val_flatmap_sound t1 t2 f l
  : (forall x, val_well_typed x t1 -> val_well_typed (f x) (ty_list t2)) ->
    val_well_typed l (ty_list t1) ->
    val_well_typed (val_flatmap f l) (ty_list t2).
Proof.
    simplify.
    induct l; simpl.
    - invert H0.
    - auto.
    - cases l1; invert H0; apply app_well_typed; eauto.
Qed.

(*
  Now that we have values, we can define our syntax of commands.
  Their purposes are as follows:
  - cmd_atom: push a value onto the stack
  - cmd_unop: pop a value from the stack, perform an unary operation on it,
              and push the result back
  - cmd_binop: pop two values from the stack, perform a binary operation on them,
              and push the result back
  - cmd_swap: switch 2 values in the stack, determined by their positions.
              `n1` must always be the earlier (smaller) position.
  - cmd_flatmap: pops a list value from the stack, runs a command `cf` on 
                 each element of the list, and appends the outputs of that 
                 command in order.
  - cmd_reduce: pops a list value and another value from the stack and accumulates
                an output value by starting with the second value and running
                a command `cf` on the current accumulator and each item in the list
                in turn.
  - cmd_skip: All other commands take the rest of the program as their final arguments.
              We use `cmd_skip` when we want to end the current command.

  You may notice that we're playing a little trick here with cmd_unop and cmd_binop.
  These cases of our stack language actually take in Rocq functions directly.
  This has some drawbacks, but it allows us to use these two constructors to add
  all sorts of operations to our language, from arithmetic to cons and ranges.
 *)
Inductive stack_cmd :=
| cmd_atom (v : stack_val) (c : stack_cmd)
| cmd_unop (f : stack_val -> stack_val) (c : stack_cmd)
| cmd_binop (f : stack_val -> stack_val -> stack_val) (c : stack_cmd)
| cmd_swap (n1 n2 : nat) (c : stack_cmd)
| cmd_flatmap (cf : stack_cmd) (c : stack_cmd)
| cmd_reduce (cf : stack_cmd) (c : stack_cmd)
| cmd_skip.

(* This is the typing judgment for commands. You should read `cmd_well_typed S c S'`
  as "On an input stack of type S, running c must produce an output stack of type S'".

  Notice that in the flatmap and reduce cases, `cf` only works with fixed input and
  output stacks. This means that it's not allowed to affect the rest of the stack,
  for example by swapping with some earlier value. *)
Inductive cmd_well_typed : list ty -> stack_cmd -> list ty -> Prop :=
| cmd_atom_wt v t S c S'
  : val_well_typed v t ->
    cmd_well_typed (t::S) c S' ->
    cmd_well_typed S (cmd_atom v c) S'
| cmd_unop_wt f t1 t2 S c S'
  : (forall v, val_well_typed v t1 -> val_well_typed (f v) t2) ->
    cmd_well_typed (t2::S) c S' ->
    cmd_well_typed (t1::S) (cmd_unop f c) S'
| cmd_binop_wt f t1 t2 t3 S c S'
  : (forall v1 v2, val_well_typed v1 t1 ->
                   val_well_typed v2 t2 ->
                   val_well_typed (f v1 v2) t3) ->
    cmd_well_typed (t3::S) c S' ->
    cmd_well_typed (t1::t2::S) (cmd_binop f c) S'
| cmd_swap_wt S n1 n2 c S'
  : n1 < n2 ->
    n2 < length S ->
    cmd_well_typed (swap n1 n2 S) c S' ->
    cmd_well_typed S (cmd_swap n1 n2 c) S'
| cmd_flatmap_wt S (cf : stack_cmd) t1 t2 c S'
  : cmd_well_typed ((ty_list t2)::S) c S' ->
    cmd_well_typed [t1] cf [ty_list t2] ->
    cmd_well_typed ((ty_list t1)::S) (cmd_flatmap cf c) S'
| cmd_reduce_wt S (cf : stack_cmd) t t_acc c S'
  : cmd_well_typed (t_acc::S) c S' ->
    cmd_well_typed [t; t_acc] cf [t_acc] ->
    cmd_well_typed ((ty_list t)::t_acc::S) (cmd_reduce cf c) S'
| cmd_skip_wt S
  : cmd_well_typed S (cmd_skip) S.
Local Hint Constructors cmd_well_typed : core.

(*
  This is our interpreter, which defines the behavior of our programs.
  Since all programs in this language terminate, we can define it as a
  regular Rocq function that takes a command and a stack and runs the
  command against the stack.
 *)
Fixpoint interp_cmd (c : stack_cmd) (s : list stack_val) : list stack_val :=
  match c with
  | cmd_atom v c' => interp_cmd c' (v::s)
  | cmd_unop f c' => interp_cmd c' (stack_unop f s)
  | cmd_binop f c' => interp_cmd c' (stack_binop f s)
  | cmd_swap n1 n2 c' => interp_cmd c' (swap n1 n2 s)
  | cmd_flatmap cf c' =>
      let (l,s1) := stack_pop s in
      let out := val_flatmap (fun x => stack_peek (interp_cmd cf [x])) l in
      interp_cmd c' (out::s1)
  | cmd_reduce cf c' => 
      let (l,s) := stack_pop s in
      let (acc,s) := stack_pop s in
      let out := val_reduce (fun acc x => stack_peek (interp_cmd cf [x;acc])) l acc in
      interp_cmd c' (out::s)
  | cmd_skip => s
  end.

(* Now let's prove that our interpreter satisfies our typing judgment.
  In other words, that running a well-typed command on a well-typed
  input stack produces a well-typed output stack.
  HINT: If you aren't sure what to do in the `cmd_reduce` case,
  look at `val_flatmap_sound` for inspiration.
  If you're really stuck, read HINT 1 in Pset6Sig.v.  *)

Lemma val_reduce_sound t1 t2 f l
  : (forall x acc', val_well_typed x t1 ->
                    val_well_typed acc' t2 ->
                    val_well_typed (f acc' x) t2) ->
    val_well_typed l (ty_list t1) ->
    forall acc,
    val_well_typed acc t2 ->
    val_well_typed (val_reduce f l acc) t2.
Proof. 
    simplify. 
    induct l; simplify; invert H0; eauto.
Qed.
    
Lemma Forall2_swap :
  forall P n1 n2 (xs: list stack_val) (ys: list ty),
    Forall2 P xs ys ->
    Forall2 P (swap n1 n2 xs) (swap n1 n2 ys).
Proof. 
    simplify.
    induct H; simplify; eauto.
Qed.

Lemma interp_sound S c S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S ->
              stack_well_typed (interp_cmd c s) S'.
Proof.
    intros H; induction H; simplify;
    (* induct 1; simplify;  *)
    try apply IHcmd_well_typed; simplify.
    - info_eauto.
    - cases s; invert H1. 
        + simplify. specialize (H s). info_eauto.
    - cases s; invert H1. 
        + cases s0; invert H7.
            * simplify. specialize (H s s0). info_eauto.
    - apply Forall2_swap with (P := val_well_typed). exact H2.
    - cases s; simplify.
        + invert H1. 
        + apply IHcmd_well_typed1. 
          invert H1. 
          econstructor.
          2: { assumption. }
          apply val_flatmap_sound with (t1 := t1). 
          2: { assumption. }
          simplify. 
          assert (stack_well_typed [x] [t1]) by (constructor; [assumption|constructor]).
          pose proof (IHcmd_well_typed2 [x] H2) as Hinterp.
          unfold stack_peek.
          cases (interp_cmd cf [x]); invert Hinterp.
            * exact H8.
    - invert H1; simplify. 
      cases l; invert H6.
      unfold stack_pop.
      apply IHcmd_well_typed1.
      econstructor; try trivial.
        + apply val_reduce_sound with (t1 := t); simplify; try trivial.
            * unfold stack_peek. 
            assert (stack_well_typed [x0; acc'] [t; t_acc]) as Hstack by eauto.
            pose proof (IHcmd_well_typed2 [x0; acc'] Hstack) as Hinterp.
            cases (interp_cmd cf [x0; acc']). invert Hinterp.
            invert Hinterp. exact H9.
    - trivial.
Qed.

(* Sometimes it's useful to combine two sequences of commands.
  Define a function `cmd_seq` so that the output is the
  concatenation of its inputs and you can prove the two following
  lemmas. *)
Fixpoint cmd_seq (c1 c2 : stack_cmd) : stack_cmd :=
  match c1 with
  | cmd_atom v c'      => cmd_atom v (cmd_seq c' c2)
  | cmd_unop f c'      => cmd_unop f (cmd_seq c' c2)
  | cmd_binop f c'     => cmd_binop f (cmd_seq c' c2)
  | cmd_swap n1 n2 c'  => cmd_swap n1 n2 (cmd_seq c' c2)
  | cmd_flatmap cf c'  => cmd_flatmap cf (cmd_seq c' c2)
  | cmd_reduce cf c'   => cmd_reduce cf (cmd_seq c' c2)
  | cmd_skip           => c2
  end.

Lemma cmd_seq_wt S1 S2 S3 c1 c2
  : cmd_well_typed S1 c1 S2 ->
    cmd_well_typed S2 c2 S3 ->
    cmd_well_typed S1 (cmd_seq c1 c2) S3.
Proof.
    simplify. induct H; simplify; eauto.
Qed. 

Lemma interp_seq c1 c2 s
  : interp_cmd (cmd_seq c1 c2) s
    = interp_cmd c2 (interp_cmd c1 s).
Proof.
    induct c1; simplify; eauto.
    induct s; simplify; unfold stack_pop; auto. 
    - destruct (stack_pop s) as [l s0] eqn:Hpop; simplify.
      destruct (stack_pop s0) as [acc s1] eqn:Hpop2; simplify.
      apply IHc1_2.
Qed.

(*
  Let's take a look at ways to optimize programs in our language.
  You may have noticed in our earlier tests that it's often convenient
  to write `stack_cmd` programs that push constants and immediately
  operate on them, or that perform a couple unops and/or binops in sequence.
  Let's take advantage of the way we defined `stack_cmd` to collapse
  those operations where possible. We'll call this "partial evaluation"
  since we're effectively interpreting portions of our command sequence
  to compute parts of the result ahead of time.

  For example, if we have a `cmd_atom` immediately followed by a
  `cmd_binop`, we want to combine the two into a `cmd_unop` by filling in
  one argument of the `cmd_binop`'s function. Take a look at the tests
  to get a better idea of this function's expected behavior.
 *)
Fixpoint partial_eval c :=
  match c with
  | cmd_atom v c' =>
      match partial_eval c' with
      | cmd_unop f c'' => cmd_atom (f v) c''
      | cmd_binop f c'' => cmd_unop (f v) c''
      | c'_fused => cmd_atom v c'_fused
      end
  | cmd_unop f c' => 
      match partial_eval c' with
      | cmd_unop g c'' => cmd_unop (fun v => g (f v)) c''
      | cmd_binop g c'' => cmd_binop (fun v1 v2 => g (f v1) v2) c''
      | c'_fused => cmd_unop f c'_fused
      end
  | cmd_binop f c' =>
      match partial_eval c' with
      | cmd_unop g c'' => cmd_binop (fun v1 v2 => g (f v1 v2)) c''
      | c'_fused => cmd_binop f c'_fused
      end
  | cmd_swap n1 n2 c' => cmd_swap n1 n2 (partial_eval c')                 
  | cmd_flatmap cf1 c' => cmd_flatmap (partial_eval cf1) (partial_eval c')
  | cmd_reduce cf c' => cmd_reduce (partial_eval cf) (partial_eval c')
  | cmd_skip => cmd_skip
  end.

(* Some common commands for use in our test cases *)
Definition val_add x y :=
  match x,y with
  | val_lit xl, val_lit yl => val_lit (xl + yl)
  | _,_ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Definition val_square x :=
  match x with
  | val_lit xl => val_lit (Nat.square xl)
  | _ => (*this case never happens on well-typed programs*) val_lit 0
  end.

Definition cmd_singleton := cmd_unop (fun x => val_cons x val_nil).
Definition cmd_lit n := cmd_atom (val_lit n).
Definition cmd_cons := cmd_binop val_cons.
Definition cmd_add := cmd_binop val_add.

Lemma partial_eval_test1
  : partial_eval (cmd_atom (val_lit 2) (cmd_unop val_square cmd_skip))
    = (cmd_atom (val_lit 4) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test2
  : partial_eval (cmd_atom (val_lit 5) (cmd_binop val_add cmd_skip))
    = (cmd_unop (val_add (val_lit 5)) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test3
  : partial_eval (cmd_unop val_square (cmd_unop val_square cmd_skip))
    = (cmd_unop (fun v => val_square (val_square v)) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test4
  : partial_eval (cmd_binop val_add (cmd_unop val_square cmd_skip))
    = (cmd_binop (fun v1 v2 => val_square (val_add v1 v2)) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test5
  : partial_eval (cmd_swap 0 2 (cmd_atom (val_lit 2) (cmd_atom (val_lit 3) (cmd_binop val_add cmd_skip))))
    = cmd_swap 0 2 (cmd_atom (val_lit 5) cmd_skip).
Proof. equality. Qed.

Lemma partial_eval_test6
  : partial_eval (cmd_unop val_square (cmd_atom (val_lit 1) (cmd_binop val_add (cmd_unop val_square cmd_skip))))
    = cmd_unop (fun x => val_square (val_add (val_lit 1) (val_square x))) cmd_skip.
Proof. equality. Qed.

Lemma partial_eval_test7
  : partial_eval (cmd_flatmap (cmd_atom (val_lit 2) (cmd_binop val_add (cmd_singleton cmd_skip)))
               (cmd_atom (val_lit 2) (cmd_unop val_square cmd_skip)))
    = cmd_flatmap (cmd_unop (fun v2 => val_cons (val_add (val_lit 2) v2) val_nil) cmd_skip)
        (cmd_atom (val_lit 4) cmd_skip).
Proof. equality. Qed.

(* With any program transformation, we want to make sure
   that it preserves all the right invariants, the most
   basic of which is type soundness, the idea that,
   given well-formed input, our optimization produces
   well-formed output.

   Since types are the focus of the next assignment,
   we've proven this for you.
 *)
Lemma partial_eval_sound S c S'
  : cmd_well_typed S c S' ->
    cmd_well_typed S (partial_eval c) S'.
Proof.
  induct 1;
    simplify;
    eauto.
  all:cases (partial_eval c);
    simplify;
    eauto.
  all: invert IHcmd_well_typed; eauto.
Qed.

(* 
  Now that we've warmed up, let's get to the meat vof this assigment,
  proving compiler correctness. Since we've defined the semantics of
  our language with an interpreter, we want to show that, given an
  arbitrary (well-typed) stack, interpreting the output of our compiler
  will give us the same result as interpreting the input. If you're having
  trouble, make sure to check the hints, as this proof is tricky.

  WARNING: For this assignment in particular, be careful of simplifying
           too early. `simplify` is helpful, but it doesn't always do what
           you want when dealing with the cases here. Our solution does
           use `simplify`, but you should specifically be cautious of
           using it after using `cases (partial_eval c)` (which will likely
           appear in your proof).

  If you're having trouble with showing that your stack has enough elements
  (e.g. in the binop case), read HINT 2 in Pset6Sig.v.
  If you're having trouble with the function argument to val_flatmap,
  read HINT 3 in Pset6Sig.v.
 *)

Lemma flatmap_funext_typed f g l t1
  : (forall v, val_well_typed v t1 -> f v = g v) ->
    val_well_typed l (ty_list t1) ->
    val_flatmap f l = val_flatmap g l.
Proof. 
    simplify. induct H0. 
    - auto. 
    - simplify. 
      pose proof (H _ H0_). rewrite H0.
      apply f_equal.
      pose proof (IHval_well_typed2 _ H).
      apply H1. trivial.
Qed. 

Lemma reduce_funext_typed f g l t1 t_acc
  : (forall v acc, 
    val_well_typed v t1 -> 
    val_well_typed acc t_acc ->
    f acc v = g acc v) ->
    (forall v acc,
        val_well_typed v t1 ->
        val_well_typed acc t_acc ->
        val_well_typed (f acc v) t_acc) ->
    val_well_typed l (ty_list t1) ->
    forall acc, 
    val_well_typed acc t_acc ->
    val_reduce f l acc = val_reduce g l acc.
Proof. 
    simplify. induct H1.
    - auto.
    - simplify. 
    pose proof (H _ _ H1_ H2). rewrite H1.
    apply IHval_well_typed2 with (t1 := t1); simplify; auto. 
    rewrite <- H1. auto.
Qed.

Lemma partial_eval_correct S c S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S -> interp_cmd (partial_eval c) s = interp_cmd c s.
Proof.
simplify. induct H; simplify.
- cases (partial_eval c); eauto.
    + simplify. apply IHcmd_well_typed with (s := v::s). auto.
    + simplify. 
      pose proof (partial_eval_sound _ _ _ H0). 
      rewrite Heq in H2.
      assert (stack_well_typed (v::s) (t::S)) by (constructor; auto).
      pose proof (IHcmd_well_typed (v::s) H3).
      rewrite <- H4.
      apply f_equal. destruct s. 
        * invert H2. invert H1. 
        * auto.
- cases (partial_eval c); 
    try (apply IHcmd_well_typed; 
    invert H1; 
    unfold stack_unop; 
    auto).
    + invert H1. 
      simplify. 
      apply IHcmd_well_typed with (s := (f x :: l)).
      auto.
    + simplify.
      pose proof (partial_eval_sound _ _ _ H0). rewrite Heq in H2.
      invert H1; subst; simplify.
      invert H2; subst; simplify.
      invert H7; subst; simplify.  
      specialize (IHcmd_well_typed ((f x)::x0::l0)).
      rewrite <- IHcmd_well_typed.
      simplify; reflexivity.
      auto.
- cases (partial_eval c); 
    try (apply IHcmd_well_typed; 
    invert H1; 
    invert H6;
    unfold stack_binop;
    auto).
    + simplify. 
      pose proof (partial_eval_sound _ _ _ H0). rewrite Heq in H2. 
      invert H1; invert H2; invert H7; subst; simplify.
      specialize (IHcmd_well_typed ((f x x0 :: l0))).
      rewrite <- IHcmd_well_typed.
      simplify; reflexivity.
      auto.
- apply IHcmd_well_typed. auto.
- destruct (stack_pop s) as [l s1] eqn:Hpop. 
  invert H1. simpl in Hpop. invert Hpop.

  assert ((val_flatmap (fun x : stack_val => stack_peek (interp_cmd (partial_eval cf) [x])) l) = (val_flatmap(fun x : stack_val => stack_peek (interp_cmd cf [x])) l)).
    apply flatmap_funext_typed with (t1:=t1) (l:= l).
    simplify. 
    apply f_equal. 
    apply IHcmd_well_typed2. 
    auto. trivial.

  rewrite H1.
  apply IHcmd_well_typed1. 
  econstructor; auto.

  apply val_flatmap_sound with (t1:=t1).
  simplify. 
    unfold stack_peek.
 
    assert (Hstack : stack_well_typed [x] [t1]) by (constructor; [exact H2 | constructor]).
    pose proof (interp_sound _ _ _ H0 [x] Hstack) as Hinterp.

    destruct (interp_cmd cf [x]) as [|y ys] eqn:Hrun; [inversion Hinterp|].
    inversion Hinterp; subst; auto.
    trivial.
- destruct (stack_pop s) as [l s0] eqn:Hpop. 
  destruct (stack_pop s0) as [acc s1] eqn:Hpop2. 
  invert H1. invert H6. 
  simpl in Hpop; invert Hpop. 
  simpl in Hpop2; invert Hpop2.

  assert ((val_reduce (fun acc0 x : stack_val => stack_peek (interp_cmd (partial_eval cf) [x; acc0])) l acc) = (val_reduce (fun acc0 x : stack_val => stack_peek (interp_cmd cf [x; acc0])) l acc)).
    { apply reduce_funext_typed with (t1:=t) (t_acc := t_acc); simplify.
      apply f_equal. 
      apply IHcmd_well_typed2. 
      auto.
      auto.
      assert (stack_well_typed [v; acc0] [t; t_acc]).   
        econstructor; trivial; auto.
      pose proof (IHcmd_well_typed2 [v; acc0] H3).
      rewrite H6. 
      pose proof (interp_sound _ _ _ H0 [v; acc0] H3).
      invert H8. auto.
      trivial. trivial. }
  rewrite H1. 
  apply IHcmd_well_typed1.
  econstructor; auto.
    Check val_reduce_sound.
  apply val_reduce_sound with (t1:=t).
  simplify. 
    unfold stack_peek.
 
    assert (Hstack : stack_well_typed [x; acc'] [t; t_acc]) by (eauto).
    pose proof (interp_sound _ _ _ H0 [x; acc'] Hstack) as Hinterp.

    cases (interp_cmd cf [x; acc']).
    inversion Hinterp; auto.
    invert Hinterp; auto.
    trivial.
    trivial.
- trivial.
Qed.

(* Let's try another compiler optimization. It turns out that when we have
  two flatmap commands in a row, we can reorder them so that the second
  one operates on each output of the first as it's produced. In other
  words, instead of generating a whole intermediate list, we can compute
  the final output as we calculate each intermediate element. This idea
  is from a family of optimizations called list fusion.

  The following lemma formalizes this idea.
  If you're having trouble with the function argument to val_flatmap,
  read HINT 4 in Pset6Sig.v.
 *)

Lemma flatmap_funext f g l :
  (forall v, f v = g v) ->
  val_flatmap f l = val_flatmap g l.
Proof.
  intros Heq; induction l; simpl; auto.
  rewrite Heq, IHl2; reflexivity.
Qed.

Lemma peek_flatmap cf s :
  stack_peek (interp_cmd (cmd_flatmap cf cmd_skip) s) =
    val_flatmap (fun y => stack_peek (interp_cmd cf [y]))
                (stack_peek s).
Proof.
  destruct s as [|a s']; simpl; reflexivity.
Qed.

Lemma val_app_assoc v1 v2 v3 :
  val_app v1 (val_app v2 v3) = val_app (val_app v1 v2) v3.
Proof.
  induction v1; simpl; auto.
  rewrite IHv1_2; reflexivity.
Qed.

Lemma val_flatmap_app g l1 l2 :
  val_flatmap g (val_app l1 l2) =
  val_app (val_flatmap g l1) (val_flatmap g l2).
Proof. 
    induct l1; auto.
    simplify. rewrite IHl1_2. apply val_app_assoc.
Qed.

Lemma val_flatmap_assoc F1 F2 l :
  val_flatmap F2 (val_flatmap F1 l)
  = val_flatmap (fun x => val_flatmap F2 (F1 x)) l.
Proof.
    induct l; simplify; auto.
    rewrite val_flatmap_app, IHl2. trivial.
Qed.

Lemma flatmap_fuse : forall cf1 cf2 c s,
    interp_cmd (cmd_flatmap cf1 (cmd_flatmap cf2 c)) s
    = interp_cmd (cmd_flatmap (cmd_seq cf1 (cmd_flatmap cf2 cmd_skip)) c) s.
Proof.
    simplify.
    destruct (stack_pop s) as [l s1] eqn:Hpop. 
    apply f_equal.
    apply (f_equal (fun x => x :: s1)).
    
    set (f := fun x =>
        stack_peek (interp_cmd (cmd_seq cf1 (cmd_flatmap cf2 cmd_skip)) [x])).
    set (g := fun x =>
        stack_peek (interp_cmd (cmd_flatmap cf2 cmd_skip) (interp_cmd cf1 [x]))).
    assert (Hfg : forall x, f x = g x).
    { intro x. unfold f, g. rewrite interp_seq. reflexivity. }
    rewrite (flatmap_funext f g l Hfg).

    assert (Hg : forall x,
        g x =
        val_flatmap (fun y => stack_peek (interp_cmd cf2 [y]))
            (stack_peek (interp_cmd cf1 [x]))).
    { intro x. subst g. apply peek_flatmap. }

    rewrite (flatmap_funext g (fun x =>
        val_flatmap (fun y => stack_peek (interp_cmd cf2 [y]))
                    (stack_peek (interp_cmd cf1 [x])))
        l Hg).

    apply val_flatmap_assoc.
Qed. 

(*
  Now, define an optimization pass that does this transformation on an
  arbitrary input command. Try to fuse as many instances of consecutive
  flatmaps as you can. You don't have to catch everything (there is one
  specific corner case that is difficult). For full credit, you should
  pass all of the test cases below without hardcoding them. If your
  definition isn't passing all of the test cases, try to compare it to
  our `partial_eval` compiler earlier and see if you're missing out on any
  chances to optimize.

  If you're having trouble with the tests, read HINT 5 in Pset6Sig.v.
 *)
Fixpoint loop_fuse (c : stack_cmd) : stack_cmd :=
  match c with
  | cmd_atom v c' => cmd_atom v (loop_fuse c')
  | cmd_unop f c' => cmd_unop f (loop_fuse c')
  | cmd_binop f c' => cmd_binop f (loop_fuse c')
  | cmd_swap n1 n2 c' => cmd_swap n1 n2 (loop_fuse c')
  | cmd_flatmap cf c' =>
      let cf_fused := loop_fuse cf in
      match loop_fuse c' with
      | cmd_flatmap cf2 c'' =>
          cmd_flatmap (cmd_seq cf_fused (cmd_flatmap cf2 cmd_skip)) c''
      | c'_fused => cmd_flatmap cf_fused c'_fused
      end
  | cmd_reduce cf c' => cmd_reduce (loop_fuse cf) (loop_fuse c')
  | cmd_skip => cmd_skip
  end.



(*
  Your loop_fuse optimizer should pass all of the following tests.
  In the event that your optimizer fuses more `cmd_flatmap`s than ours
  and this causes one or more of these tests to fail, admit the failing test,
  add a corresponding passing test, and explain why the second output is superior.
 *)

Lemma loop_fuse_test1
  : loop_fuse (cmd_flatmap (cmd_singleton (cmd_lit 0 (cmd_cons cmd_skip)))
                 (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip))) cmd_skip))
    = (cmd_flatmap (cmd_singleton
                      (cmd_lit 0
                         (cmd_cons
                            (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip)))
                               cmd_skip))))
         cmd_skip).
Proof. equality. Qed.

Lemma loop_fuse_test2
  : loop_fuse (cmd_flatmap (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                              (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                                 (cmd_singleton cmd_skip)))
                 cmd_skip)
    = cmd_flatmap
         (cmd_flatmap
            (cmd_unop val_square
               (cmd_singleton
                  (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                     cmd_skip)))
            (cmd_singleton cmd_skip))
         cmd_skip.
Proof. equality. Qed.

Lemma loop_fuse_test3
  : loop_fuse (cmd_flatmap (cmd_unop val_square (cmd_singleton cmd_skip))
                 (cmd_flatmap (cmd_singleton (cmd_lit 0 (cmd_cons cmd_skip)))
                 (cmd_flatmap (cmd_lit 1 (cmd_add (cmd_singleton cmd_skip))) cmd_skip)))
    = cmd_flatmap
        (cmd_unop val_square
           (cmd_singleton
              (cmd_flatmap
                 (cmd_singleton
                    (cmd_atom (val_lit 0)
                       (cmd_binop val_cons
                          (cmd_flatmap
                             (cmd_atom (val_lit 1)
                                (cmd_binop val_add (cmd_singleton cmd_skip)))
                             cmd_skip))))
                 cmd_skip)))
        cmd_skip.
Proof. equality. Qed.

(* As a first step, let's prove that this optimization preserves
   our typing judgment like before. The proof will be very similar
   to the one for `op_fuse`.
 *)
Lemma loop_fuse_sound S c S'
  : cmd_well_typed S c S' ->
    cmd_well_typed S (loop_fuse c) S'.
Proof.
  induct 1; simplify; eauto.
  cases (loop_fuse c); simplify; eauto.
  rewrite <- Heq in IHcmd_well_typed1.
  (* Where is `op_fuse`?? It is not in the textbook nor the 
     homework repo. *)
Admitted.

(*
  Now for the largest proof of the pset, let's prove that `loop_fuse` is correct.
  Make sure you've attempted `op_fuse_correct` first since the proof is similar
  and relies on some of the same lemmas.
 *)
Lemma loop_fuse_correct S c S'
  : cmd_well_typed S c S' ->
    forall s, stack_well_typed s S -> interp_cmd (loop_fuse c) s = interp_cmd c s.
Proof.
Admitted.



End Impl.

Module ImplCorrect : Pset6Sig.S := Impl.

(* Authors:
  Dustin Jamner
  Paul Mure
*)
