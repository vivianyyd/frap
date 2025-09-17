(** * 6.512 Formal Reasoning About Programs, Fall 2025 - Pset 1 *)

(* Welcome to 6.512!  Read through `Pset1Signature.v` before starting here. *)

Require Import Frap Pset1Signature.

Module Impl.
  (* The first part of this assignment involves the [bool] datatype,
   * which has the following definition.
   * <<
       Inductive bool :=
       | true
       | false.
     >>
   * We will define logical negation and conjunction of Boolean values,
   * and prove some properties of these definitions.
   *)

  (* Define [Neg] so that it implements Boolean negation, which flips
   * the truth value of a Boolean value.
   *)
  Definition Neg (b : bool) : bool :=
  match b with
    | true => false
    | false => true
    end.

  (* For instance, the negation of [true] should be [false].
   * This proof should follow from reducing both sides of the equation
   * and observing that they are identical.
   *)
  Theorem Neg_true : Neg true = false.
  Proof.
    simplify.
    equality.
  Qed.

  (* Negation should be involutive, meaning that if we negate
   * any Boolean value twice, we should get the original value back.

   * To prove a fact like this that holds for all Booleans, it suffices
   * to prove the fact for both [true] and [false] by using the
   * [cases] tactic.
   *)
  Theorem Neg_involutive : forall b : bool, Neg (Neg b) = b.
  Proof.
    intros b.
    cases b; simplify; equality.
  Qed.

  (* Define [And] so that it implements Boolean conjunction. That is,
   * the result value should be [true] exactly when both inputs
   * are [true].
   *)
  Definition And (x y : bool) : bool :=
  match x with 
  |true => match y with 
    |true => true
    |false => false
    end
  | false => false
  end.

  (* Here are a couple of examples of how [And] should act on
   * concrete inputs.
   *)
  Theorem And_true_true : And true true = true.
  Proof.
  simplify. equality.
  Qed.

  Theorem And_false_true : And false true = false.
  Proof.
    simplify. equality.
    Qed.

  (* Prove that [And] is commutative, meaning that switching the order
   * of its arguments doesn't affect the result.
   *)
  Theorem And_comm : forall x y : bool, And x y = And y x.
  Proof.
    intros x y.
    cases x; cases y; equality.
  Qed.

  (* Prove that the conjunction of a Boolean value with [true]
   * doesn't change that value.
   *)
  Theorem And_true_r : forall x : bool, And x true = x.
  Proof.
    intros x.
    cases x; equality.
  Qed.

  (* You may have noticed that the [=] operator above does not return a [bool]. *)
  Check (true = false).
  
  (* [a = b] is instead a [Prop], short for proposition, the type of logical
   * statements. The set of propositions in Rocq is large and contains a variety
   * of statements, many of which are undecideable, so we can't in general
   * treat statements in [Prop] as functions with Boolean output. This means
   * that you can't use expressions of type [Prop] when defining a program,
   * since they don't have computational behavior. For example, compare how
   * the following two expressions evaluate. The first expression uses functions
   * we can compute with, while the second uses propositions:
   *)
  Compute (if 1 ==n 2 then (And true false) else true).
  Compute (1 = 2 -> True /\ False).
  
  (* The following operations that you have seen or will see soon are in [Prop],
   * so they cannot be used in if-then-else statements:
   * - [a = b] (equality at an arbitrary type)
   * - [a <= b] (a less than or equal to b for natural numbers)
   * - [a < b] (a less than b for natural numbers)
   * - [a >= b] (a greater than or equal to b for natural numbers)
   * - [a > b] (a greater than b for natural numbers)
   * - [a <> b] (inequality at an arbitrary type)
   * - [a /\ b] (propositional conjunction)
   * - [~ a] (propositional negation)
   *
   * These operations are defined as functions, so you can evalute them:
   * - [a ==n b] (decidable equality for natural numbers)
   * - [a ==v b] (decidable equality for variables)
   * - [And a b] (Boolean conjunction, defined above)
   * - [Neg a] (Boolean negation, defined above)
   *
   * To see an example of what can go wrong, uncommment the following [Compute] command
   * and note the reported error message.
   *)
  
  (* Compute if 0 < 1 then 0 else 1. *)

  (* The correct boolean version. *)
  Compute if Nat.ltb 0 1 then 0 else 1.
  
  (* In the second part of this assignment, we will work with a simple language
   * of imperative arithmetic programs that sequentially apply operations
   * to a natural-number-valued state.
   * 
   * Remember that we are working with natural division which rounds down.
   * Note the output of these [Compute] commands.
   *)
  
  Compute 3 / 3.
  Compute 2 / 3.
  Compute 4 / 3.
  
  (*

   * The [Prog] datatype defines abstract syntax trees for this language.
   *)

  Print Prog.

  (* Define [run] such that [run p n] gives the final state
   * that running the program [p] should result in, when the
   * initial state is [n].
   *)
  Fixpoint run (p : Prog) (initState : nat) : nat :=
  match p with 
  | Done => initState
  | AddThen n c => run c (n + initState)
  | MulThen n c => run c (n * initState)
  | DivThen n c => run c (initState / n)
  | VidThen n c => run c (n / initState) 
  | SetToThen n c => run c n
  end.

  Theorem run_Example1 : run Done 0 = 0.
  Proof.
    simplify. equality.
  Qed.

  Theorem run_Example2 : run (MulThen 5 (AddThen 2 Done)) 1 = 7.
  Proof.
    simplify. equality.
  Qed.

  Theorem run_Example3 : run (SetToThen 3 (MulThen 2 Done)) 10 = 6.
  Proof.    
    simplify. equality.
  Qed.

  (* Define [numInstructions] to compute the number of instructions
   * in a program, not counting [Done] as an instruction.
   *)
  Fixpoint numInstructions (p : Prog) : nat :=
  match p with 
  | Done => 0
  | AddThen _ c => 1 + numInstructions c
  | MulThen _ c => 1 + numInstructions c
  | DivThen _ c => 1 + numInstructions c
  | VidThen _ c => 1 + numInstructions c
  | SetToThen _ c => 1 + numInstructions c
  end.

  Theorem numInstructions_Example :
    numInstructions (MulThen 5 (AddThen 2 Done)) = 2.
  Proof.
    simplify. equality.
  Qed.

  (* Define [concatProg] such that [concatProg p1 p2] is the program
   * that first runs [p1] and then runs [p2].
   *)
  Fixpoint concatProg (p1 p2 : Prog) : Prog :=
  match p1 with 
  | Done => p2
  | AddThen   n c => AddThen n (concatProg c p2)
  | MulThen   n c => MulThen   n (concatProg c p2)
  | DivThen   n c => DivThen   n (concatProg c p2)
  | VidThen   n c => VidThen   n (concatProg c p2)
  | SetToThen n c => SetToThen n (concatProg c p2)
  end.

  Theorem concatProg_Example :
       concatProg (AddThen 1 Done) (MulThen 2 Done)
       = AddThen 1 (MulThen 2 Done).
  Proof.
    simplify. equality.
  Qed.

  (* Prove that the number of instructions in the concatenation of
   * two programs is the sum of the number of instructions in each
   * program.
   *)
  Theorem concatProg_numInstructions
    : forall (p1 p2 : Prog), numInstructions (concatProg p1 p2)
                        = numInstructions p1 + numInstructions p2.
  Proof.
    intros p1 p2.
    induct p1; simplify; equality.
  Qed.

  (* Prove that running the concatenation of [p1] with [p2] is
     equivalent to running [p1] and then running [p2] on the
     result. *)
  Theorem concatProg_run
    : forall (p1 p2 : Prog) (initState : nat),
      run (concatProg p1 p2) initState =
      run p2 (run p1 initState).
  Proof.
    intros p1 p2.
    induct p1; simplify; equality.
  Qed.

  (* Read this definition and understand how division by zero is handled. *)
  Fixpoint runPortable (p : Prog) (state : nat) : bool * nat :=
    match p with
    | Done => (true, state)
    | AddThen n p => runPortable p (n+state)
    | MulThen n p => runPortable p (n*state)
    | DivThen n p =>
        if n ==n 0 then (false, state) else
        runPortable p (state/n)
    | VidThen n p =>
        if state ==n 0 then (false, 0) else
        runPortable p (n/state)
    | SetToThen n p =>
        runPortable p n
    end.
  Arguments Nat.div : simpl never. (* you don't need to understand this line *)

  (* Here are a few examples: *)

  Definition goodProgram1 := AddThen 1 (VidThen 10 Done).
  Example runPortable_good : forall n,
    runPortable goodProgram1 n = (true, 10/(1+n)).
  Proof. simplify. equality. Qed.

  Definition badProgram1 := AddThen 0 (VidThen 10 Done).
  Example runPortable_bad : let n := 0 in
    runPortable badProgram1 n = (false, 0).
  Proof. simplify. equality. Qed.

  Definition badProgram2 := AddThen 1 (DivThen 0 Done).
  Example runPortable_bad2 : forall n,
    runPortable badProgram2 n = (false, 1+n).
  Proof. simplify. equality. Qed.

  (* Prove that running the concatenation [p] using [runPortable]
     coincides with using [run], as long as [runPortable] returns
     [true] to confirm that no divison by zero occurred. *)
  Lemma runPortable_run : forall p s0 s1,
    runPortable p s0 = (true, s1) -> run p s0 = s1.
  Proof. 
    induct p.
    simplify; try equality; apply IHp; try exact H.
    simplify; try equality; apply IHp; try exact H.
    simplify; try equality; apply IHp; try exact H.

    simplify. induct n. 
        simplify. equality.
        simplify. apply IHp. exact H.

    simplify. apply IHp. induct s0. 
        simplify. equality.
        exact H.

    simplify; try equality; apply IHp; try exact H.
  Qed.

  (* The final goal of this pset is to implement [validate : Prog -> bool]
     such that if this function returns [true], the program would not trigger
     division by zero regardless of what state it starts out in.  [validate] is
     allowed to return [false] for some perfectly good programs that never cause
     division by zero, but it must recognize as good the examples given below.  In
     jargon, [validate] is required to be sound but not complete, but "complete
     enough" for the use cases defined by the examples given here: *)

  Definition goodProgram2 := AddThen 0 (MulThen 10 (AddThen 0 (DivThen 1 Done))).
  Definition goodProgram3 := AddThen 1 (MulThen 10 (AddThen 0 (VidThen 1 Done))).
  Definition goodProgram4 := Done.
  Definition goodProgram5 := SetToThen 0 (DivThen 1 Done).
  Definition goodProgram6 := SetToThen 1 (VidThen 1 Done).
  Definition goodProgram7 := AddThen 1 (DivThen 1 (DivThen 1 (VidThen 1 Done))).

  (* If you already see a way to build [validate] that meets the
   * requirements above, _and have a plan for how to prove it correct_,
   * feel free to just code away. Our solution uses one intermediate definition
   * and one intermediate lemma in the soundness proof -- both of which are more
   * sophisticated than the top-level versions given here. *)

  (* If a clear plan hasn't emerged in 10 minutes (or if you get stuck later),
   * take a look at the hints for this pset at the end of the signature file.
   * It is not expected that this pset is doable for everyone without the hints,
   * and some planning is required to complete the proof successfully.
   * In particular, repeatedly trying out different combinations of tactics
   * and ideas from hints until something sticks can go on for arbitrarily long
   * with little insight and no success; just guessing a solution is unlikely.
   * Thus, we encourage you to take your time to think, look at the hints when
   * necessary, and only jump into coding when you have some idea why it should
   * succeed. Some may call Rocq a video game, but it is not a grinding contest. *)

  Fixpoint validate' (p: Prog) (nz: bool) : bool :=
  match p with 
  | Done => true
  | AddThen n c => validate' c (if n ==n 0 then nz else true)
  | MulThen n c => validate' c (if n ==n 0 then false else nz)
  | DivThen n c => if n ==n 0 then false else validate' c (if n ==n 1 then nz else false) (* n can be arbitrarily large, making division produce zero state *)
  | VidThen n c => if nz then validate' c false (* state can be arbitrarily large, making n/state 0 *) else false
  | SetToThen n c => validate' c (if n ==n 0 then false else true)
  end.

  Definition validate (p : Prog) : bool := validate' p false.
  
  (* Start by making sure that your solution passes the following tests, and add
   * at least one of your own tests: *)

  Example validate1 : validate goodProgram1 = true. Proof. simplify. equality. Qed.
  Example validate2 : validate goodProgram2 = true. Proof. simplify. equality. Qed.
  Example validate3 : validate goodProgram3 = true. Proof. simplify. equality. Qed.
  Example validate4 : validate goodProgram4 = true. Proof. simplify. equality. Qed.
  Example validate5 : validate goodProgram5 = true. Proof. simplify. equality. Qed.
  Example validate6 : validate goodProgram6 = true. Proof. simplify. equality. Qed.
  Example validate7 : validate goodProgram7 = true. Proof. simplify. equality. Qed.
  Example validateb1 : validate badProgram1 = false. Proof. simplify. equality. Qed.
  Example validateb2 : validate badProgram2 = false. Proof. simplify. equality. Qed.

  (* Then, add your own example of a bad program here, and check that `validate`
   * returns `false` on it: *)
  Definition test (p: Prog): Prop := validate p = fst (runPortable p 0).

  Definition badProgram3 := SetToThen 1 (DivThen 0 Done).
  Example validateb3 : validate badProgram3 = false. Proof. simplify. equality. Qed.
  Example valid1 : test badProgram3. Proof. compute. equality. Qed.

  Definition bad2 := SetToThen 1 (DivThen 3 (VidThen 10 Done)).
  Example valid2 : test bad2. Proof. compute. equality. Qed.

  Definition ok1 := SetToThen 1 (DivThen 3 Done).
  Example valid3: test ok1. Proof. compute. equality. Qed.
  
  Definition bad3 := SetToThen 10 (VidThen 1 (VidThen 2 Done)).
  Example valid4: test bad3. Proof. compute. equality. Qed.

  (* Finally, before diving into the Rocq proof, try to convince yourself that
   * your code is correct by applying induction by hand.  Can you describe the
   * high-level structure of the proof?  Which cases will you have to reason
   * about?  What do the induction hypotheses look like?  Which key lemmas do
   * you need?  Write a short (~10-20 lines) informal proof sketch before
   * proceeding. *)

  (** Proof sketch: **)
  (* 
    By definition of validate, it suffices to show that whenever validate' p false 
    returns true, the program p never divides by zero.
    We'll proceed by induction on the program, and break the proof goal into the 
    conjunction of two cases - one where the state is nonzero, and the other where 
    it is not necessarily nonzero. When we do induction, we can split the IHp into
    separate clauses in order to apply it. Then for each possible program node, we
    need to show that it preserves the invariant between nz and s. 
    We'll do this by simply calling IHp, which requires us to prove two premises
    about nz and s before we are allowed to conclude the result. 
   *)

  (* Now you're ready to write the proof in Rocq: *)

  Lemma P (p: Prog) :
    (validate' p true = true ->
        forall s, s <> 0 -> runPortable p s = (true, run p s)) /\
    (validate' p false = true ->
        forall s, runPortable p s = (true, run p s)).
  Proof. 
    induct p; 
    split; simplify; try equality; simplify; destruct IHp.

    destruct (n ==n 0); apply H1. try apply H; linear_arithmetic.
    cases n; simplify; linear_arithmetic; apply H; try linear_arithmetic. apply H; linear_arithmetic.
    destruct (n ==n 0). linear_arithmetic. cases n; simplify; linear_arithmetic. 
    destruct (n ==n 0). apply H1. apply H. apply H0. apply H. cases n; simplify; linear_arithmetic.

    destruct (n ==n 0). apply H2; apply H. apply H1. apply H. linear_arithmetic.
    destruct (n ==n 0); apply H1; apply H. 

    destruct (n ==n 0). exfalso. discriminate H.
    destruct (n ==n 1). 
        apply H1. apply H. subst n. rewrite Nat.div_1_r. apply H0.
        apply H2. apply H.

    destruct (n ==n 0). exfalso. discriminate H.
    destruct (n ==n 1). 
        apply H1. apply H. apply H1. apply H.
    destruct (s ==n 0). exfalso. apply H0. exact e.

    apply H2. apply H. cases (n ==n 0). apply H2. apply H. apply H1. apply H. apply n0.

    cases (n ==n 0). apply H1. apply H. apply H0. apply H. apply n0. 
  Qed.

  Lemma validate_sound : forall p, validate p = true ->
    forall s, runPortable p s = (true, run p s).
  Proof.
    simplify.
    unfold validate in H.
    apply P. exact H. 
  Qed.

  (* Here is the complete list of commands used in one possible solution:
    - Search, for example Search (_ + 0).
    - induct, for example induct x
    - simplify
    - propositional
    - equality
    - linear_arithmetic
    - cases, for example cases (X ==n Y)
    - apply, for example apply H
    - apply in, for example apply H1 in H2 or apply somelemma in H1
    - apply with, for example apply H1 with (x:=2)
    - apply in with, for example apply H1 with (x:=2) in H2
    - rewrite, for example rewrite H
    - rewrite in, for example rewrite H1 in H2 or rewrite somelemma in H1
    - ;, for example simplify; propositional *)
End Impl.

(* The following line checks that your `Impl` module implements the right
   signature.  Make sure that it works, or the auto-grader will break!
   If there are mismatches, Rocq will report them (`Signature components for
   label … do not match`): *)
Module ImplCorrect : Pset1Signature.S := Impl.
