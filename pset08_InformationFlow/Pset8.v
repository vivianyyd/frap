(*|
==========================================================
 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 8
==========================================================
|*)

Require Import Pset8.Pset8Sig.

(*|
Introduction
============

Computer programs commonly manipulate data from different sources, at different
levels of privacy or trust. An e-commerce website, for example, might keep track
of the contents of each individual cart, and it would be a severe issue if one user
got access to the content of another user's cart.

Such “information-flow” issues are of a different nature from the functionality bugs
that we usually think of, but they are also pervasive and tricky to detect and fix:
for example, for a few weeks in 2011, Facebook's abuse-reporting tool made it possible
to access a user's private photos by reporting one of their *public* photos for abuse:
the tool would then conveniently offer to report other photos, *including private ones*
that the reporter was not allowed to access.
(https://www.zdnet.com/article/facebook-flaw-allows-access-to-private-photos/)

In this pset, we will see how type systems can help with information-flow issues.
We will operate in a simplified setting in which all information is either
“public” or “private”, and we will concern ourselves only with *confidentiality*,
the property that private inputs should not influence public program outputs.

Informally, we'll prove the correctness of a type system such that type-safe programs
do not leak private data: that is, we'll prove that changing the private inputs of
a well-typed program does not change its public outputs. We'll say that well-typed
programs are “confidential”.

Note that this formulation doesn't rule out side channels: changing the private inputs
of a program might change its runtime or even whether it terminates.

Language definition
===================

This is as usual:
|*)

Module Impl.
Inductive bop := Plus | Minus | Times.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Bop (b : bop) (e1 e2 : arith).

Coercion Const : nat >-> arith.
Coercion Var : var >-> arith.
Declare Scope  arith_scope.
Notation "a + b" := (Bop Plus a b) : arith_scope.
Notation "a - b" := (Bop Minus a b) : arith_scope.
Notation "a * b" := (Bop Times a b) : arith_scope.
Delimit Scope arith_scope with arith.

Inductive cmd :=
| Skip
| Assign (x : var) (e : arith)
| Sequence (c1 c2 : cmd)
| If (e : arith) (thn els : cmd)
| While (e : arith) (body : cmd).

(* Here are some notations for the language, which again we won't really explain. *)
Notation "x <- e" := (Assign x e%arith) (at level 75).
Infix ";;" := Sequence (at level 76). (* This one changed slightly, to avoid parsing clashes. *)
Notation "'when' e 'then' thn 'else' els 'done'" := (If e%arith thn els) (at level 75, e at level 0).
Notation "'while' e 'loop' body 'done'" := (While e%arith body) (at level 75).

(*|
Program semantics
=================

And the semantics of the language are as expected; the language is made deterministic
by defaulting to 0 when a variable is undefined.
|*)

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Bop bp e1 e2 =>
    match bp with
    | Plus => Nat.add
    | Minus => Nat.sub
    | Times => Nat.mul
    end (interp e1 v) (interp e2 v)
  end.

Inductive eval : valuation -> cmd -> valuation -> Prop :=
| EvalSkip : forall v,
    eval v Skip v
| EvalAssign : forall v x e,
    eval v (Assign x e) (v $+ (x, interp e v))
| EvalSeq : forall v c1 v1 c2 v2,
    eval v c1 v1
    -> eval v1 c2 v2
    -> eval v (Sequence c1 c2) v2
| EvalIfTrue : forall v e thn els v',
    interp e v <> 0
    -> eval v thn v'
    -> eval v (If e thn els) v'
| EvalIfFalse : forall v e thn els v',
    interp e v = 0
    -> eval v els v'
    -> eval v (If e thn els) v'
| EvalWhileTrue : forall v e body v' v'',
    interp e v <> 0
    -> eval v body v'
    -> eval v' (While e body) v''
    -> eval v (While e body) v''
| EvalWhileFalse : forall v e body,
    interp e v = 0
    -> eval v (While e body) v.
(* Local Hint Constructors eval : core. *)

(*|
Typing judgment
===============

The `Confidential` judgment below indicates that a program respects confidentiality.
It takes a set of public variables and a command and returns a `Prop` indicating whether
the program is safe. Take the time to understand exactly how `Confidential` works
(or, even better, take a few moments to think about how you would define a `Confidential` predicate).

In full generality, an information-flow system associates a label to each variable.
We'll simplify things and classify variables as “public” or “private”, and instead of
having a map giving the label of each value, we'll keep track of the set of all public variables.

First, we need a way to collect the variables of an expression
(We haven't seen the `set` type too often; see the tips in ``Pset8Sig.v`` for a quick recap).
|*)

Fixpoint vars (e: arith) : set var :=
  match e with
  | Const n => {} (** A constant has no variables **)
  | Var x => {x} (** A variable has… one variable! **)
  | Bop _ e1 e2 => vars e1 \cup vars e2 (** An operator's variables are the variables of its subterms **)
  end.

(*|
The parameter `pub` below represents the set of all public variables.
This is predeclared and fixed. But there is also a distinct `set var` argument.
This is because we need to consider *implicit* as well as *explicit* flows.

- An explicit flow happens when assigning to a variable.
  If `e` mentions variable `x`, then `y := e` may cause data to flow from `x` into `y`. 
  If `x` is private and `y` is public, we want to rule that out.

- An implicit flow happens when assigning to a variable *under a conditional*.
  If `e` mentions variable `x`, then `when e then y := 1` may cause data to flow
  from `x` to `y` (can you see why?). There, too, if `x` is private and `y` is public,
  we want to disallow this flow.

This is why we have the second `set var` (`cv`) argument below:
In addition to the set of public variables, we keep track of the set of variables
from which data may flow implicitly via their effect on control flow.
We call that set “cv”, for “control variables”.
|*)

Inductive Confidential (pub: set var) : set var (* cv *) -> cmd (* program *) -> Prop :=
| ConfidentialSkip : forall cv,
    Confidential pub cv Skip
(** A `Skip` is safe. **)
| ConfidentialAssignPrivate : forall cv x e,
    ~ x \in pub ->
    Confidential pub cv (Assign x e)
(** Assigning to a private variable is safe. **)
| ConfidentialAssignPublic : forall cv x e,
    vars e \subseteq pub ->
    cv \subseteq pub ->
    Confidential pub cv (Assign x e)
(** Assigning to a public variable variable is safe as long as
    the expression does not mention private variables and
    we are not under a conditional that depends on private variables. **)
| ConfidentialSeq : forall cv c1 c2,
    Confidential pub cv c1 ->
    Confidential pub cv c2 ->
    Confidential pub cv (Sequence c1 c2)
(** A sequence is safe if both halves of it are safe. **)
| ConfidentialIf : forall cv e thn els,
    Confidential pub (cv \cup vars e) thn ->
    Confidential pub (cv \cup vars e) els ->
    Confidential pub cv (If e thn els)
(** A conditional is safe if both branches are safe,
    noting that the branches run with additional variables in the `cv`. **)
| ConfidentialWhile : forall cv e body,
    Confidential pub (cv \cup vars e) body ->
    Confidential pub cv (While e body).
(** A while loop is safe if its body is safe,
    noting that the body runs with additional variables in the `cv`. **)
Local Hint Constructors Confidential : core.
(*|
Here are a few examples:
|*)

Definition pub_example := {"x", "y", "z"}. (* Variables x, y, z are public. *)

Example confidential_prog :=
  ("x" <- "y" + 1;;
   "a" <- "a" * "b";;
   when "y" then "a" <- 0 else "b" <- 0 done).

Goal Confidential pub_example {} confidential_prog.
Proof.
  unfold confidential_prog, pub_example.
  apply ConfidentialSeq; simplify.
  - apply ConfidentialSeq; simplify.
    + apply ConfidentialAssignPublic; simplify.
      * sets.
      * sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
  - apply ConfidentialIf; simplify.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
    + apply ConfidentialAssignPrivate; simplify.
      sets.
Qed.

Example leaky_prog :=
  (when "a" then "x" <- 1 else "x" <- 2 done).

Goal ~ Confidential pub_example {} leaky_prog.
Proof.
  unfold leaky_prog, pub_example, not; simplify.
  invert H; simplify.
  invert H3; simplify.
  - sets.
  - pose proof @subseteq_In _ "a" _ _ H4.
    sets.
Qed.

(*|
Proof of noninterference
=========================

We first need a relation to characterize “equivalent” valuations — that is,
valuations that agree on all public variables.
`restrict s m` means restrict the valuation `m` to just the keys in `s`:
|*)

Definition same_public_state pub (v1 v2: valuation) :=
  restrict pub v1 = restrict pub v2.

(* Before we get started proving properties of our type system, please read
   Pset8Sig.v and consider the questions below. The only graded question is
   the multiple-choice one, but we are assigning the rest in hopes that they
   help you complete the following parts.

 Suppose an expression contains only public variables. Under what valuations 
 do we expect them to evaluate to the same value?

 All valuations with the same public state

 Suppose an expression evaluates to different values under different
 valuations. What do we know about this expression if the different valuations
 share the same public state? Do we know anything if the valuations do not 
 share the same public state?

 That means the expression leaks information from private variables. 
 This is still the case if the public states are different, but the variables in the
 diff are not mentioned in the expression.
 However, if the expressions literally have different public variables, we don't 
 really learn anything about the private variables

 The noninterference property says that running a program in states with 
 private variables holding potentially different values does not change the 
 public outputs of the program.

 The key difficulty is to deal with *divergence* — the cases where the two 
 program executions take different paths.

 When does this happen?  How does that translate in terms of the variables
 in `cv`?
 
 This happens when we do a branch as in when or while. It matters because if
 we're in a branch conditioned on a private variable, we can't assign to public
 stuff or else information about this private control variable will leak. 

 Can a divergent execution affect the values of public variables?

 Yes, as I just mentioned and as is shown in the example leaky_prog. 

 When a Confidential program executes, in what ways can it modify the 
 valuation? How does this depend on the values of `cv`?

 It can modify private variables freely. It can only assign to public variables if 
 the current branch is only dependent on public variables. 

 Finally, can the value of a private variable (one not in `pub`) determine
 whether a confidential program terminates? Assign the definition below to
 `true` if so, and `false` if not.

 From the intro: 
We'll prove that changing the private inputs of
a well-typed program does not change its public outputs. We'll say that well-typed
programs are “confidential”.
Note that this formulation doesn't rule out side channels: changing the private inputs
of a program might change its runtime or even whether it terminates.

See the below test. 
 *)

Definition private_can_determine_termination : bool := true.

Example test :=
 ("a" <- 1;; while "a" loop Skip done).

Goal Confidential pub_example {} test.
Proof.
 unfold test, pub_example.
 apply ConfidentialSeq; simplify.
 - apply ConfidentialAssignPublic; simplify; sets.
 - apply ConfidentialWhile; simplify.
   + apply ConfidentialSkip; simplify.
Qed.


(* HINT 1-2 (see Pset8Sig.v) *) 

Lemma restrict_with_pub :
  forall pub (v1 v2: valuation) x e,
    restrict pub v1 = restrict pub v2 ->
    x \in pub ->
    restrict pub (v1 $+ (x, e)) = restrict pub (v2 $+ (x, e)).
Proof. 
    simplify. 
    maps_equal.
    cases (k ==v x).
    - rewrite e0.
      rewrite !lookup_restrict_true by assumption.
      rewrite !lookup_add_eq; trivial.
    - excluded_middle (k \in pub).
        + rewrite !lookup_restrict_true by assumption.
          rewrite !lookup_add_ne by assumption.
          rewrite <- (lookup_restrict_true pub v1 k) by assumption.
          rewrite <- (lookup_restrict_true pub v2 k) by assumption.
          rewrite H.
          equality.
        + rewrite !lookup_restrict_false by assumption.
          equality.
Qed.

Lemma restrict_not_pub :
  forall pub (v1 v2 : valuation) x e e',
    restrict pub v1 = restrict pub v2 ->
    ~ pub x ->
    restrict pub (v1 $+ (x, e)) = restrict pub (v2 $+ (x, e')).
Proof.
  simplify.
  maps_equal.
  cases (k ==v x); simplify; try equality.
  excluded_middle (k \in pub).
  - rewrite !lookup_restrict_true by assumption.
    rewrite !lookup_add_ne by assumption.
    rewrite <- (lookup_restrict_true pub v1 k) by assumption.
    rewrite <- (lookup_restrict_true pub v2 k) by assumption.
    rewrite H.
    equality.
  - rewrite !lookup_restrict_false by assumption.
    equality.
Qed.

(* If an expression uses only some set of variables, it evaluates to the same value under any valuations that have the same assignments to that set.  *)
Lemma public_expr_equal :
  forall pub e v1 v2,
    same_public_state pub v1 v2 ->
    vars e \subseteq pub ->
    interp e v1 = interp e v2.
Proof.
    induct e; simplify; trivial.

    unfold same_public_state in H.
    assert (x \in pub) by sets.
    assert (v1 $? x = v2 $? x).
    rewrite <- (lookup_restrict_true pub v1 x) by assumption.
    rewrite <- (lookup_restrict_true pub v2 x) by assumption.
    rewrite H; trivial.
    destruct (v1 $? x); rewrite <- H2; trivial.

    assert ((vars e1) \subseteq pub) by sets.
    assert ((vars e2) \subseteq pub) by sets.
    pose proof (IHe1 _ _ H H1).
    pose proof (IHe2 _ _ H H2).
    rewrite H3.
    rewrite H4. 
    equality.
Qed.

Lemma non_interference_cvs :
  forall pub c cv v1 v1' v2 v2',
    eval v1 c v1' ->
    eval v2 c v2' ->
    Confidential pub cv c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof. 
induct c; simplify.
    - invert H.
      invert H0.
      trivial.
    - invert H. 
      invert H0.
      invert H1. 
        + unfold same_public_state in H2.
          unfold same_public_state. 
          apply restrict_not_pub;
          trivial.
        + unfold same_public_state.
          excluded_middle (x \in pub).
            * assert (interp e v1 = interp e v2) by 
              (apply public_expr_equal with (pub := pub); 
              trivial).
              rewrite H0.
              apply restrict_with_pub;
              trivial.
            * apply restrict_not_pub; trivial. 
    - invert H. 
      invert H0.
      invert H1.
      pose proof (IHc1 _ _ _ _ _ H6 H5 H4 H2).
      pose proof (IHc2 _ _ _ _ _ H8 H9 H7 H).
      trivial.
    - pose proof H. 
      pose proof H0.
      pose proof H1.
      invert H;
      invert H0;
      invert H1.
        + pose proof (IHc1 _ _ _ _ _ H12 H13 H7 H2); trivial.
        + admit. 
        
        
Admitted.

Theorem non_interference :
  forall pub c v1 v1' v2 v2',
    eval v1 c v1' ->
    eval v2 c v2' ->
    Confidential pub {} c ->
    same_public_state pub v1 v2 ->
    same_public_state pub v1' v2'.
Proof.
    simplify. 
    apply (non_interference_cvs _ _ _ _ _ _ _ H H0 H1 H2).
Qed.

(*|
Congratulations, you have proved that our type system is *sound*: it catches all leaky programs!
But it is not *complete*: there are some good programs that it rejects, too.
In other words, it *overapproximates* the set of unsafe programs.

Can you give an example of a safe program (a program that does not leak data) that our system
would reject?
|*)

Definition tricky_example : cmd :=
(when "a" then "x" <- 1;; "x" <- 0 else "x" <- 0 done).

Lemma tricky_rejected : ~ Confidential pub_example {} tricky_example.
Proof.
    unfold tricky_example, pub_example, not; simplify.
    invert H. invert H3. invert H5. sets.
    unfold vars in H6. assert ("a" \in {"x", "y", "z"}) by sets. sets.
Qed.

Lemma tricky_confidential :
  forall v1 v1' v2 v2',
    eval v1 tricky_example v1' ->
    eval v2 tricky_example v2' ->
    same_public_state pub_example v1 v2 ->
    same_public_state pub_example v1' v2'.
Proof.
    unfold tricky_example, pub_example; simplify.
    invert H; invert H0.
    - invert H8. invert H9. invert H3. invert H4.
      invert H5. 
      invert H10. trivial.
      unfold same_public_state.
      assert (interp 1 v1 = interp 1 v2) by trivial.
      rewrite !H.
      apply restrict_with_pub; sets.
      apply restrict_with_pub; sets.
    - invert H8. invert H9. invert H3. invert H5.
      unfold same_public_state.
      assert (interp 0 (v1 $+ ("x", interp 1 v1)) = 0) by trivial.
      assert (interp 0 v2 = 0) by trivial.
      rewrite H. 
      rewrite H0.
      assert ((v1 $+ ("x", interp 1 v1) $+ ("x", 0)) = (v1 $+ ("x", 0))) by sets.
      rewrite H2.
      trivial.
      apply restrict_with_pub; trivial; sets.
    - invert H8. invert H9. invert H3. invert H5.
      unfold same_public_state.
      assert ((v2 $+ ("x", interp 1 v2) $+ ("x", interp 0 (v2 $+ ("x", interp 1 v2)))) = (v2 $+ ("x", 0))) by sets; trivial.
      rewrite H. 
      replace (interp 0 v1) with 0 by trivial.
      apply restrict_with_pub; trivial; sets.
    - invert H9. invert H8.
      replace (interp 0 v1) with 0 by trivial.
      replace (interp 0 v2) with 0 by trivial.
      apply restrict_with_pub; trivial; sets.
Qed.
End Impl.

Module ImplCorrect : Pset8Sig.S := Impl.

(* Authors:
   Clément Pit-Claudel
   Dustin Jamner
 *)
