(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 7 *)

Require Import Frap.Frap.
Require Import Pset7.Pset7Sig.

(* The following line forces you to use bullets or braces.  Remove it if you get
   errors like "Expected a single focused goal but 2 goals are focused." and you
   don't want to structure your proofs. *)
Set Default Goal Selector "!".
Set Implicit Arguments.

Module Impl.
(** * Subtyping *)

(* We can't resist fitting in another crucial aspect of type systems:
 * *subtyping*, which formalizes when any value of one type should also be
 * permitted as a value of some other type. Languages like Java include
 * *nominal* subtyping, based on declared type hierarchies. Instead, here we
 * will prove the soundness of *structural* subtyping, whose rules we'll get to
 * shortly. The simply typed lambda calculus will be our starting point. *)

(* Expression syntax *)
Inductive exp  :=
(* Our old friends from simply typed lambda calculus *)
| Var (x : var)
| Abs (x : var) (e1 : exp)
| App (e1 e2 : exp)

(* New features, surrounding *tuple* types, which build composite types out of
 * constituents *)
| TupleNil
(* Empty tuple (no fields) *)
| TupleCons (e1 e2 : exp)
(* Nonempty tuple, where [e1] is the first field of the tuple, and [e2] is a
 * nested tuple with all the remaining fields *)

| Proj (e : exp) (n : nat)
(* Grab the [n]th field of tuple [e]. *)
.

(* Values (final results of evaluation) *)
Inductive value : exp -> Prop :=
| VAbs : forall x e1, value (Abs x e1)
| VTupleNil : value TupleNil
| VTupleCons : forall e1 e2, value e1 -> value e2 -> value (TupleCons e1 e2)
.
Local Hint Constructors value : core.

(* The next few definitions are quite routine and should be safe to skim through
 * quickly; but start paying more attention when we get to defining the
 * subtyping relation! *)

(* Substitution (not capture-avoiding, for the usual reason) *)
Fixpoint subst (e1 : exp) (x : var) (e2 : exp) : exp :=
  match e2 with
  | Var y => if y ==v x then e1 else Var y
  | Abs y e2' => Abs y (if y ==v x then e2' else subst e1 x e2')
  | App e2' e2'' => App (subst e1 x e2') (subst e1 x e2'')
  | TupleNil => TupleNil
  | TupleCons e2' e2'' => TupleCons (subst e1 x e2') (subst e1 x e2'')
  | Proj e2' n => Proj (subst e1 x e2') n
  end.

(* Evaluation contexts *)
Inductive context :=
| Hole
| App1 (C : context) (e2 : exp)
| App2 (v1 : exp) (C : context)
| TupleCons1 (C : context) (e2 : exp)
| TupleCons2 (v1 : exp) (C : context)
| Proj1 (C : context) (n : nat)
.

(* Plugging an expression into a context *)
Inductive plug : context -> exp -> exp -> Prop :=
| PlugHole : forall e, plug Hole e e
| PlugApp1 : forall e e' C e2,
    plug C e e'
    -> plug (App1 C e2) e (App e' e2)
| PlugApp2 : forall e e' v1 C,
    value v1
    -> plug C e e'
    -> plug (App2 v1 C) e (App v1 e')
| PlugTupleCons1 : forall C e e' e2,
    plug C e e'
    -> plug (TupleCons1 C e2) e (TupleCons e' e2)
| PlugTupleCons2 : forall v1 C e e',
    value v1
    -> plug C e e'
    -> plug (TupleCons2 v1 C) e (TupleCons v1 e')
| PlugProj : forall C e e' n,
    plug C e e'
    -> plug (Proj1 C n) e (Proj e' n)
.
Local Hint Constructors plug: core.


(* Small-step, call-by-value evaluation *)
Inductive step0 : exp -> exp -> Prop :=
| Beta : forall x e v,
    value v
    -> step0 (App (Abs x e) v) (subst v x e)

(* To project field 0 out of a tuple, just grab the first component. *)
| Proj0 : forall v1 v2,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) 0) v1

(* To project field [1+n], drop the first component and continue with [n]. *)
| ProjS : forall v1 v2 n,
    value v1
    -> value v2
    -> step0 (Proj (TupleCons v1 v2) (1 + n)) (Proj v2 n)
.
Local Hint Constructors step0 : core.

Inductive step : exp -> exp -> Prop :=
| StepRule : forall C e1 e2 e1' e2',
    plug C e1 e1'
    -> plug C e2 e2'
    -> step0 e1 e2
    -> step e1' e2'.
Local Hint Constructors step : core.

Definition trsys_of (e : exp) :=
  {| Initial := {e}; Step := step |}.

(* Syntax of types *)
Inductive type :=
| Fun (dom ran : type)
| TupleTypeNil
| TupleTypeCons (t1 t2 : type)
.
Local Hint Constructors type : core.

Inductive subtype : type -> type -> Prop :=

(* Two function types are related if their components are related pairwise.
 * Counterintuitively, we *reverse* the comparison order for function domains!
 * It may be worth working through some examples to see why the relation would
 * otherwise be unsound. *)
| StFun : forall t1' t2' t1 t2,
    subtype t1 t1' ->
    subtype t2' t2 ->
    subtype (Fun t1' t2') (Fun t1 t2)

(* An empty tuple type is its own subtype. *)
| StTupleNilNil :
    subtype TupleTypeNil TupleTypeNil

(* However, a nonempty tuple type is also a subtype of the empty tuple type.
 * This rule gives rise to *width* subtyping, where we can drop some fields of
 * a tuple type to produce a subtype. *)
| StTupleNilCons : forall t1 t2,
    subtype (TupleTypeCons t1 t2) TupleTypeNil

(* We also have *depth* subtyping: we can replace tuple components with
 * subtypes. *)
| StTupleCons : forall t1' t2' t1 t2,
    subtype t1' t1 ->
    subtype t2' t2 ->
    subtype (TupleTypeCons t1' t2') (TupleTypeCons t1 t2)
.

(* Here's a more compact notation for subtyping. *)
Infix "$<:" := subtype (at level 70).

Local Hint Constructors subtype : core.

(* Projecting out the nth field of a tuple type *)
Inductive proj_t : type -> nat -> type -> Prop :=
| ProjT0 : forall t1 t2,
    proj_t (TupleTypeCons t1 t2) 0 t1
| ProjTS : forall t1 t2 n t,
    proj_t t2 n t ->
    proj_t (TupleTypeCons t1 t2) (1 + n) t
.
Local Hint Constructors proj_t : core.

(* Expression typing relation stating something _has_ a _ty_pe *)
Inductive has_ty : fmap var type -> exp -> type -> Prop :=
| HtVar : forall G x t,
    G $? x = Some t ->
    has_ty G (Var x) t
| HtAbs : forall G x e1 t1 t2,
    has_ty (G $+ (x, t1)) e1 t2 ->
    has_ty G (Abs x e1) (Fun t1 t2)
| HtApp : forall G e1 e2 t1 t2,
    has_ty G e1 (Fun t1 t2) ->
    has_ty G e2 t1 ->
    has_ty G (App e1 e2) t2
| HtTupleNil : forall G,
    has_ty G TupleNil TupleTypeNil
| HtTupleCons: forall G e1 e2 t1 t2,
    has_ty G e1 t1 ->
    has_ty G e2 t2 ->
    has_ty G (TupleCons e1 e2) (TupleTypeCons t1 t2)
| HtProj : forall G e n t t',
    has_ty G e t' ->
    proj_t t' n t ->
    has_ty G (Proj e n) t

(* This is the crucial rule: when an expression has a type, it also has any
 * supertype of that type. We call this rule *subsumption*. *)
| HtSub : forall G e t t',
    has_ty G e t' ->
    t' $<: t ->
    has_ty G e t
.
Local Hint Constructors has_ty : core.


(* Before we get started proving properties of our type system, please read
 * Pset7Sig.v and consider the questions below. This task is ungraded,
 * but we are assigning it in hopes it helps you complete the
 * following parts.

 What does it mean for the subtyping order of the arguments in `StFun` to be 
 reversed?

 Functions have contravariant subtyping. Intuitively, it makes sense that if the output of a function is t and t <: t', then the output can also be considered type t'.
 But just because function's input can be type t and t <: t', that doesn't mean the
 function is able to process values of type t', since there are things of type t'
 but not of type t.

 If t1 $<: t2, what is known about some t3 that is a supertype of t2? And 
 likewise if it's a subtype of t1?

 t1 <: t3. and t3 <: t2. In other words, transitivity


 How many goals do you get from calling `invert` on a hypothesis like
 ```
 has_ty G (Abs x e1) t
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `has_ty`, and what 
 information do you have about `t`?

  Only the HtAbs constructor can produce this, so invert produces a single goal. 
 We get types t1 and t2 with t = Fun t1 t2, and the premise has_ty (G $+ (x, t1)) e1 t2
 
 
 To contrast, how many goals do you expect with the `has_ty` definition of
 this pset? Why is this the case? 

 Here we have two goals. One is the same as the version from class, but the other one considers that the type of e1 is a subtype of the function's input type.

 Can you formulate a lemma that consolidates the information present in these 
 branches into one conclusion? (Imagine inverting now is equivalent to an
 "or" generating branches for each constructor; can you rephrase a lemma that
 leads to a conclusion with an "and" instead?)

  forall G x e1 t,
    has_ty G (Abs x e1) t ->
    exists t1 t2,
      has_ty (G $+ (x, t1)) e1 t2 /\ Fun t1 t2 $<: t.

 How many goals do you get from calling `invert` on a hypothesis like
 ```
 has_ty G e (Fun t1 t2)
 ```
 with the `LambdaCalculusAndTypeSoundness` definition of `has_ty`, and what 
 information do you have about `e`? 

3 goals. That's because there are three cases. We could've gotten a function because it was in the context as such. In that case, we know e is a variable. We could also have a function type since it's an abstraction. In that case, we know it's a lambda with type t1->t2. We could also get a function since e is some application App e1 e2, then we'd have that has_ty G e1 (Fun t_arg (Fun t1 t2)) and has_ty G e2 t_arg for some t_arg.

 To contrast, how many goals do you expect with the `has_ty` definition 
 of this pset? Why is this the case? 

 We also have all the same branches and two additional ones. First, we could've gotten the function from projecting out from a tuple. Second, we once again have the subtyping case.

Can you formulate a lemma to recover information similar to what inverting
 gave you in FRAP's `has_ty` definition?

  forall G e t1 t2,
    has_ty G e (Fun t1 t2) ->
    exists t1' t2',
      has_ty G e (Fun t1' t2') /\
      Fun t1' t2' $<: Fun t1 t2 /\
      (forall x, e = Var x ->
         G $? x = Some (Fun t1' t2')) /\
      (forall x e1, e = Abs x e1 ->
         has_ty (G $+ (x, t1')) e1 t2') /\
      (forall e1 e2, e = App e1 e2 ->
         exists t_arg,
           has_ty G e1 (Fun t_arg (Fun t1' t2')) /\
           has_ty G e2 t_arg) /\
      (forall e' n, e = Proj e' n ->
         exists t', has_ty G e' t' /\ proj_t t' n (Fun t1' t2')).

*)

(* Prove these two basic algebraic properties of subtyping. *)

Lemma subtype_refl : forall t1, t1 $<: t1.
Proof.
  induct t1; simplify.
  - apply StFun; assumption.
  - apply StTupleNilNil.
  - apply StTupleCons; assumption.
Qed.


(* BEGIN handy tactic that we suggest for these proofs *)
Ltac tac0 :=
  match goal with
  | [ H : ex _ |- _ ] => invert H
  | [ H : _ /\ _ |- _ ] => invert H
  | [ |- context[_ $+ (?x, _) $? ?y] ] => cases (x ==v y); simplify
  | [ |- context[?x ==v ?y] ] => cases (x ==v y); simplify
  | [ H : step _ _ |- _ ] => invert H
  | [ H : step0 _ _ |- _ ] => invert1 H
  | [ H : has_ty _ _ _ |- _ ] => invert1 H
  | [ H : proj_t _ _ _ |- _ ] => invert1 H
  | [ H : plug _ _ _ |- _ ] => invert1 H
  | [ H : subtype _ _ |- _ ] => invert1 H
  | [ H : Some _ = Some _ |- _ ] => invert H
  end;
  subst.

Ltac tac := simplify; subst; propositional; repeat (tac0; simplify); try equality.
(* END handy tactic *)

(* HINT 1 (see Pset7Sig.v) *) 

Definition P (t1 t2 : type) : Prop :=
  (forall t3, t2 $<: t3 -> t1 $<: t3)
  /\ (forall t0, t0 $<: t1 -> t0 $<: t2).

Lemma subtype_trans_aux : forall t1 t2, t1 $<: t2 -> P t1 t2.
Proof.
    simplify. 
    induct H; 
    unfold P; 
    tac; eauto; 
    unfold P in IHsubtype1, IHsubtype2; 
    simplify; 
    propositional; 
    try (apply StFun; auto); 
    try (apply StTupleCons; auto).
    - invert H1; auto.
Qed.

Lemma subtype_trans : forall t1 t2 t3, t1 $<: t2 -> t2 $<: t3 -> t1 $<: t3.
Proof.
  simplify.
  revert t3 H0.
  induction H; intros t3 H23; invert H23; eauto.
  rename t1' into a3.
  rename t2' into b1.
  rename t0 into a1.
  rename t4 into b3.
  rename t1 into a2.
  rename t2 into b2.
  pose proof (subtype_trans_aux).
  pose proof (fun t1 t2 Hsub => proj1 (H1 t1 t2 Hsub)) as H_forward.
  pose proof (fun t1 t2 Hsub => proj2 (H1 t1 t2 Hsub)) as H_backward.
  apply StFun.
  { apply H_forward with (t2 := a2); trivial. }
  { auto. }
Qed.

(* The real prize: prove soundness of this type system.
 * We suggest starting from a copy of the type-safety proof from the book's
 * EvaluationContexts.v.
 * The soundness argument for simply typed lambda calculus is genuinely difficult
 * (a celebrated result!). We're not expecing you to reinvent it. Rather, the
 * task of this pset is to *extend* it to cover subtyping. This will involve
 * changing some proofs and making appropriate additional helper lemmas (there
 * are more hints in Pset7Sig.v).
*)

Lemma canonical_fun :
  forall G e t1 t2,
    has_ty G e (Fun t1 t2) ->
    value e ->
    exists x e',
      e = Abs x e'.
Proof.
    simplify. propositional. induct H.
    - inversion H0.
    - exists x, e1. propositional.
    - inversion H1.
    - inversion H1. 
    - inversion H0.
      apply IHhas_ty with (t1 := t1') (t2 := t2'); 
      auto.
Qed.

Lemma canonical_tuple :
  forall G e t1 t2,
    has_ty G e (TupleTypeCons t1 t2) ->
    value e ->
    exists v1 v2,
      e = TupleCons v1 v2 /\
      value v1 /\ value v2.
Proof.
    simplify. propositional. induct H.
    - inversion H0.
    - inversion H1. 
    - inversion H1. exists e1, e2. auto.
    - inversion H1. 
    - inversion H0. 
      apply IHhas_ty with (t1 := t1') (t2 := t2'); auto.
Qed.

Lemma step_of_step0 :
  forall e e', step0 e e' -> step e e'.
Proof.
  intros e e' Hstep0.
  eapply StepRule with (C := Hole)
                       (e1 := e) (e2 := e')
                       (e1' := e) (e2' := e'); auto using PlugHole.
Qed.
Local Hint Resolve step_of_step0.

(* HINT 2-3 (see Pset7Sig.v) *) 
Lemma progress : forall e t,
    has_ty $0 e t
    -> value e
    \/ (exists e' : exp, step e e').
Proof.
induct 1; eauto.
- right. 
  specialize (IHhas_ty1 eq_refl).
  cases IHhas_ty1; cases IHhas_ty2. 
  + pose proof (canonical_fun H IHhas_ty1). 
    destruct H1 as [x [e' Heq]].
    exists (subst e2 x e').
    apply step_of_step0.
    rewrite Heq. 
    eauto. 
  + destruct IHhas_ty2.
    exists (App e1 x).
    inversion H1. 
    apply StepRule with (C :=  App2 e1 C) (e1 := e0) (e2 := e3);
    auto. 
  + destruct IHhas_ty1.
    inversion H1.
    exists (App x e2).
    apply StepRule with (C := App1 C e2) (e1 := e0) (e2 := e3);
    auto.
  + destruct IHhas_ty1.
    inversion H1.
    exists (App x e2).
    apply StepRule with (C := App1 C e2) (e1 := e0) (e2 := e3);
    auto.
- specialize (IHhas_ty1 eq_refl).
  cases IHhas_ty1; cases IHhas_ty2.
  + left; auto.
  + right. 
    destruct IHhas_ty2.
    inversion H1. 
    exists (TupleCons e1 x).
    apply StepRule with (C := TupleCons2 e1 C) (e1 := e0) (e2 := e3); auto.
  + right.
    destruct IHhas_ty1.
    inversion H1. 
    exists (TupleCons x e2).
    apply StepRule with (C := TupleCons1 C e2) (e1 := e0) (e2 := e3); auto.
  + right.
    destruct IHhas_ty1.
    inversion H1. 
    exists (TupleCons x e2).
    apply StepRule with (C := TupleCons1 C e2) (e1 := e0) (e2 := e3); auto.
- right.
  invert H0;
  cases IHhas_ty.
  + pose proof (canonical_tuple) H IHhas_ty; 
    destruct H0 as [v1 [v2 [Heq [val1 val2]]]].
    exists v1. 
    apply step_of_step0.
    rewrite Heq.
    auto.
  + destruct IHhas_ty.
    exists (Proj x 0).
    inversion H0.
    apply StepRule with (C := Proj1 C 0) (e1 := e1) (e2 := e2); 
    auto. 
  + pose proof (canonical_tuple) H IHhas_ty; 
    destruct H0 as [v1 [v2 [Heq [val1 val2]]]].
    exists (Proj v2 n0).
    apply step_of_step0.
    rewrite Heq.
    auto.
  + destruct IHhas_ty.
    exists (Proj x (1 + n0)).
    inversion H0.
    apply StepRule with (C := Proj1 C (1 + n0)) (e1 := e1) (e2 := e2); 
    auto. 
Qed. 

Lemma weakening_override : forall (G G' : fmap var type) x t,
(forall x' t', G $? x' = Some t' -> G' $? x' = Some t')
-> (forall x' t', G $+ (x, t) $? x' = Some t'
                    -> G' $+ (x, t) $? x' = Some t').
Proof.
simplify.
cases (x ==v x'); simplify; eauto.
Qed.

Local Hint Resolve weakening_override : core.

Lemma weakening : forall G e t,
has_ty G e t
-> forall G', (forall x t, G $? x = Some t -> G' $? x = Some t)
    -> has_ty G' e t.
Proof.
induct 1; simplify; tac; eauto 6.
Qed.

Local Hint Resolve weakening : core.

(* Replacing a typing context with an equal one has no effect (useful to guide
* proof search as a hint). *)
Lemma has_ty_change : forall G e t,
has_ty G e t
-> forall G', G' = G
    -> has_ty G' e t.
Proof. tac. Qed.

Local Hint Resolve has_ty_change : core.

Lemma substitution : forall G x t' e t e',
has_ty (G $+ (x, t')) e t
-> has_ty $0 e' t'
-> has_ty G (subst e' x e) t.
Proof. induct 1; tac; eauto. Qed.
Local Hint Resolve substitution : core.


Lemma has_ty_TupleCons G e e' t:
   has_ty G (TupleCons e e') t ->
   exists t1 t2, has_ty G e t1 /\ has_ty G e' t2 /\ TupleTypeCons t1 t2 $<: t.
Proof. Admitted.

Lemma preservation0 : forall e1 e2,
step0 e1 e2
-> forall t, has_ty $0 e1 t
    -> has_ty $0 e2 t.
Proof.
invert 1; tac.
(* - eapply substitution.
    + invert H.
        * invert H4. {eapply H2. } *)
(*
Preservation proof runs by inversion on the primitive step and relies on the inversion lemmas for typing plus substitution and subtyping facts.

Beta: From has_ty $0 (App (Abs x e) v) t, use the App inversion lemma (parallel to has_ty_TupleCons in Pset7.v:...) to get t1, t2, typings of the operands, and Fun t1 t2 $<: t. The Abs inversion lemma yields has_ty ($0 $+ (x, t1)) e t2; substitution gives has_ty $0 (subst v x e) t2, and the saved subtyping derivation lifts the result to t.

Proj0: Projection inversion on has_ty $0 (Proj (TupleCons v1 v2) 0) t produces a witness TupleTypeCons t1 t2 $<: t; the tuple inversion lemma recovers typings for v1 and v2, and reflexivity of subtyping delivers has_ty $0 v1 t.

ProjS: Projection inversion plus has_ty_TupleCons again expose types for the tuple components and the residual projection. Reassemble the typing derivation for Proj v2 n, then apply the collected subtyping proof to reach t.

Each branch therefore constructs has_ty $0 e2 t, completing preservation for step0.
*)
invert H.
    + invert H4; apply substitution with (t' := t1); auto.
    
        * apply substitution .
 (* apply substitution with (t' := t1). *)
    + invert H. 
        * invert H4. { eapply H2. }
info_eauto 6.
Qed.
(* 

Local Hint Resolve preservation0 : core.

Lemma preservation' : forall C e1 e1',
    plug C e1 e1'
    -> forall e2 e2' t, plug C e2 e2'
    -> step0 e1 e2
    -> has_ty $0 e1' t
    -> has_ty $0 e2' t.
Proof.
induct 1; t.
Qed.
Local Hint Resolve preservation' : core.


    HINT 3: Helper lemmas for preservation: Typing inversion
In the proof of preservation for `step0`, you will have `has_ty` hypotheses for for expressions with known constructors, e.g. for an `(Abs x e)` or for a `(TupleCons e1 e2)` etc.
Without subtyping, inverting such a `has_ty` would give you just one subgoal, where the `has_ty` is replaced by the preconditions that were used to construct it.
Now, with subtyping, you get one additional subgoal for the `HtSub` case, where the original `has_ty` is replaced by a similar looking `has_ty` and a subtyping derivation. You could invert that new `has_ty` again, and again and again, and your proving endeavor would never end.
This hint shows how to solve this problem for `TupleCons`, but you will have to apply this trick for all constructors of `exp`.
Without subtyping, we would know that if `TupleCons e1 e2` has a type t, then there are some types t1 and t2 such that e1 has type t1, e2 has type t2, and `t = TupleTypeCons t1 t2`. This fact would follow directly from the fact that there is only a single rule for typing a TupleCons expression.
However, once we add subtyping, the HtSub rule allows us to type an expression of any form, and so the above property doesn't hold. A typing derivation for the fact that `TupleCons e1 e2` has type t can be arbitrarily long even when e1 and e2 are small, but we still know that it must start from an application of the HtTupleCons rule, followed by potentially many applications of the HtSub rule. Since we have proven that the subtype relation is reflexive and transitive, we know the many applications of the HtSub rule can be replaced with exactly one, meaning we know that there is a derivation for TupleCons e1 e2 that is an HtSub rule applied to the HtTupleCons rule. This tells us the following fact:
Lemma has_ty_TupleCons G e e' t:
   has_ty G (TupleCons e e') t ->
   exists t1 t2, has_ty G e t1 /\ has_ty G e' t2 /\ TupleTypeCons t1 t2 $<: t.
Knowing this fact is useful for the type-safety proof, because now whenever we know that `TupleCons e e'` has some type, we can directly get information about the types of its subexpressions. If we only tried to invert the original typing derivation, the last rule in the derivation may have been HtSub, in which case we would make no "progress" down towards finding the application of the rule HtTupleCons.
You should be able to formulate and prove similar lemmas for Abs, App, and Proj.


   *)
  Lemma preservation : forall e1 e2,
    step e1 e2
    -> forall t, has_ty $0 e1 t
      -> has_ty $0 e2 t.
  Proof.
    admit.
    (* invert 1; t. *)
  Admitted.

  Local Hint Resolve progress preservation : core.

(* Theorem safety : forall e t, has_ty $0 e t
    -> invariantFor (trsys_of e)
                    (fun e' => value e'
                               \/ exists e'', step e' e'').
  Proof.
    simplify.
    apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t); eauto.
    apply invariant_induction; simplify; eauto; equality.
  Qed. *)

Theorem safety : forall e t, has_ty $0 e t
  -> invariantFor (trsys_of e)
                  (fun e' => value e'
                            \/ exists e'', step e' e'').
Proof.
   simplify.
    apply invariant_weaken with (invariant1 := fun e' => has_ty $0 e' t); eauto.
    - apply invariant_induction; simplify; eauto.
        + destruct H0; subst; auto. exfalso; auto.
Qed.

End Impl.

(* The following line checks that your `Impl` module implements the right
   signature. Make sure that it works, or the auto-grader will break!
   If there are mismatches, Rocq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset7Sig.S := Impl.

(* Authors:
 * Peng Wang
 * Adam Chlipala
 * Samuel Gruetter
 * Amanda Liu
 * Paul Mure
 *)
